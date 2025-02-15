﻿//=========================================================================
// Copyright 2009 Sergey Antonov <sergant_@mail.ru>
// 
// This software may be used and distributed according to the terms of the
// GNU General Public License version 2 as published by the Free Software
// Foundation.
// 
// See the file COPYING.TXT for the full text of the license, or see
// http://www.gnu.org/licenses/gpl-2.0.txt
// 
//=========================================================================

using System;
using System.Collections.Generic;
using System.Text;
using System.IO;
using System.Diagnostics;
using System.Windows.Forms;
using HgSccHelper.CommandServer;

namespace HgSccHelper
{
	//-----------------------------------------------------------------------------
	public class FackedCheckoutInfo
	{
		public string File { get; set; }
	}

	//-----------------------------------------------------------------------------
	public class HgScc : IDisposable
	{
		public string WorkingDir { get; private set; }
		public List<string> SubRepoDirs { get; private set; } 
		private HgClient hg_client;

		//-----------------------------------------------------------------------------
		public HgScc()
		{
			hg_client = new HgClient();
			SubRepoDirs = new List<string>();
		}

		//-----------------------------------------------------------------------------
		public HgClient Client
		{
			get { return hg_client; }
		}

		//-----------------------------------------------------------------------------
		public bool GetRelativePath(string path, out string relative)
		{
			return Util.GetRelativePath(WorkingDir, path, out relative);
		}

		//-----------------------------------------------------------------------------
		public string GetRootPath(string local_proj_path)
		{
			return new Hg().Root(local_proj_path);
		}

		//-----------------------------------------------------------------------------
		public SccErrors OpenProject(string local_proj_path, SccOpenProjectFlags flags)
		{
			Logger.WriteLine("OpenProject: {0}, flags {1}", local_proj_path, flags);

			var hg = new Hg();
			string root = hg.Root(local_proj_path);
			bool is_root_exist = !String.IsNullOrEmpty(root);

			if (!is_root_exist)
			{
				Logger.WriteLine("Root not exists");

				if ((flags & SccOpenProjectFlags.CreateIfNew) == SccOpenProjectFlags.CreateIfNew)
				{
					Logger.WriteLine("Creating a repository: {0}", local_proj_path);

					if (!hg.CreateRepository(local_proj_path))
						return SccErrors.CouldNotCreateProject;

					Logger.WriteLine("Repository created");
					root = local_proj_path;
				}
				else
				{
					if ((flags & SccOpenProjectFlags.SilentOpen) == SccOpenProjectFlags.SilentOpen)
						return SccErrors.UnknownProject;

					return SccErrors.NonSpecificError;
				}
			}

			WorkingDir = root;
			string hgsubPath = Path.Combine(root, ".hgsub");
			if (File.Exists(hgsubPath))
			{
				Logger.WriteLine("Found .hgsub");
				using (StreamReader reader = new StreamReader(hgsubPath))
				{
					while (!reader.EndOfStream)
					{
						string line = reader.ReadLine();
						if (string.IsNullOrEmpty(line)) continue;

						string[] tokens = line.Split('=');
						if (tokens.Length > 1)
						{
							SubRepoDirs.Add(tokens[0].Trim().Replace('/','\\'));
						}
					}
				}
			}

			try
			{
				Logger.WriteLine("Opening a command server client: {0}", local_proj_path);
				if (!hg_client.Open(WorkingDir))
				{
					Logger.WriteLine("Unable to connect to command server: {0}", WorkingDir);
					hg_client.Dispose();

					return SccErrors.NonSpecificError;
				}
			}
			catch (Exception ex)
			{
				Logger.WriteLine("Exception : {0}", ex.Message);
				Logger.WriteLine("StackTrace: {0}", ex.StackTrace);
				throw;
			}

			return SccErrors.Ok;
		}

		//-----------------------------------------------------------------------------
		public SccErrors CloseProject()
		{
			return SccErrors.Ok;
		}

		//-----------------------------------------------------------------------------
		private static SccStatus ToSccStatus(HgFileStatus status)
		{
			SccStatus scc = SccStatus.None;
			switch (status)
			{
				case HgFileStatus.Added: scc |= SccStatus.Controlled | SccStatus.CheckedOut | SccStatus.OutByUser | SccStatus.Modified; break;
				case HgFileStatus.Clean: scc |= SccStatus.Controlled; break;
				case HgFileStatus.Deleted: scc |= SccStatus.Controlled | SccStatus.Deleted; break;
				case HgFileStatus.Ignored: scc |= SccStatus.NotControlled; break;
				case HgFileStatus.Modified: scc |= SccStatus.Controlled | SccStatus.CheckedOut | SccStatus.OutByUser | SccStatus.Modified; break;
				case HgFileStatus.NotTracked: scc |= SccStatus.NotControlled; break;
				case HgFileStatus.Removed: scc |= SccStatus.Controlled | SccStatus.Deleted; break;
				case HgFileStatus.Tracked: scc |= SccStatus.Controlled; break;
				default:
					scc = SccStatus.Invalid;
					break;
			}

			return scc;
		}

/*
		//-----------------------------------------------------------------------------
		public SccErrors LookupProjects(string folder, out SccFileInfo[] files)
		{
			var dict = new Dictionary<string, bool>();
			dict.Add(".sln", true);
			dict.Add(".atp", true);
			dict.Add(".dbp", true);
			dict.Add(".vap", true);
			dict.Add(".vsproj", true);
			dict.Add(".vbdproj", true);
			dict.Add(".vddproj", true);
			dict.Add(".dbproj", true);
			dict.Add(".vbp;*.vip;*.vbproj", true);
			dict.Add(".vcproj", true);
			dict.Add(".vdproj", true);
			dict.Add(".vmx", true);
			dict.Add(".vup", true);
			dict.Add(".csproj", true);

			string[] all_files = Directory.GetFiles(folder);
			var found_list = new List<string>();
			foreach (var f in all_files)
			{
				string ext = Path.GetExtension(f).ToLower();
				if (dict.ContainsKey(ext))
					found_list.Add(f);
			}

			string[] found_files = found_list.ToArray();
			files = new SccFileInfo[found_files.Length];
			
			for (int i = 0; i < found_files.Length; ++i)
			{
				files[i] = new SccFileInfo { File = Path.GetFullPath(found_files[i]), Status = SccStatus.None };
				Logger.WriteLine("-> " + files[i].File);
			}

			return QueryInfo(files);
		}
*/

		//-----------------------------------------------------------------------------
		public Dictionary<string, HgFileInfo> QueryInfoFullDict()
		{
			var dict = new Dictionary<string, HgFileInfo>();
			foreach (var file_status in hg_client.Status())
			{
				dict.Add(file_status.File, file_status);
			}

			return dict;
		}

		//------------------------------------------------------------------
		public SccErrors QueryInfo2(HgFileInfo[] files)
		{
			// TODO: Check if project is opened
			var lst = new List<string>();

			foreach (var f in files)
			{
				string file;
				if (Util.GetRelativePath(WorkingDir, f.File, out file))
					lst.Add(file);
			}

			var stats = hg_client.Status(lst);

			var dict = new Dictionary<string, HgFileInfo>();
			foreach (var file_status in stats)
			{
				string file = file_status.File.ToLower();
				dict.Add(file, file_status);
			}

			foreach (var info in files)
			{
				HgFileInfo file_info;
				string file;
				if (	Util.GetRelativePath(WorkingDir, info.File, out file)
					&& dict.TryGetValue(file.ToLower(), out file_info)
					)
				{
					info.CopiedFrom = file_info.CopiedFrom;
					info.Status = file_info.Status;
				}
				else
				{
					info.Status = HgFileStatus.NotTracked;
				}
			}

			return SccErrors.Ok;
		}

		//-----------------------------------------------------------------------------
		public SccErrors Add(IntPtr hwnd, SccAddFile[] files, string comment)
		{
			var lst = new List<string>();
			foreach (var f in files)
				lst.Add(f.File);

			return Add(hwnd, lst);
		}

		//-----------------------------------------------------------------------------
		public SccErrors Add(IntPtr hwnd, IEnumerable<string> files)
		{
			// TODO: Check if project is opened
			var add_files = new List<string>();

			foreach (var file in files)
			{
				string f;
				if (!GetRelativePath(file, out f))
					return SccErrors.InvalidFilePath;

				add_files.Add(f);
			}

			if (add_files.Count > 0)
			{
				if (!hg_client.Add(add_files))
					return SccErrors.OpNotPerformed;
			}
			return SccErrors.Ok;
		}

		//-----------------------------------------------------------------------------
		public SccErrors Copy(IntPtr hwnd, string dest_path, string src_path, bool is_after_copy_occured)
		{
			string local_dest;
			string local_src;
			
			if (!GetRelativePath(src_path, out local_src))
				return SccErrors.InvalidFilePath;

			if (!GetRelativePath(dest_path, out local_dest))
				return SccErrors.InvalidFilePath;

			var options = is_after_copy_occured ? HgCopyOptions.After : HgCopyOptions.None;
			if (!hg_client.Copy(local_dest, local_src, options))
				return SccErrors.OpNotPerformed;

			return SccErrors.Ok;
		}

		//-----------------------------------------------------------------------------
		public SccErrors CommitAll(IntPtr hwnd, string comment)
		{
			if (!hg_client.CommitAll(HgCommitOptions.None, comment).IsSuccess)
				return SccErrors.OpNotPerformed;

			return SccErrors.Ok;
		}

		//-----------------------------------------------------------------------------
		public SccErrors CommitAll(IntPtr hwnd, string comment, string date_str)
		{
			if (!hg_client.CommitAll(HgCommitOptions.None, comment, date_str).IsSuccess)
				return SccErrors.OpNotPerformed;

			return SccErrors.Ok;
		}

		//-----------------------------------------------------------------------------
		public SccErrors Revert(IntPtr hwnd, IEnumerable<string> files, out IEnumerable<string> reverted_files)
		{
			var local_files = new List<string>();
			var to_revert = new List<string>(files);
			reverted_files = to_revert;

			// FIXME: Add dialog with checkboxes
			foreach (var f in to_revert)
			{
				string local_f;
				if (!GetRelativePath(f, out local_f))
					return SccErrors.InvalidFilePath;

				local_files.Add(local_f);
			}

			if (local_files.Count > 0)
			{
				if (!hg_client.Revert(local_files))
					return SccErrors.NonSpecificError;
			}

			return SccErrors.Ok;
		}

		//-----------------------------------------------------------------------------
		public bool Checkout(string file, string rev, string temp_file)
		{
			return hg_client.CheckoutFile(file, "", temp_file);
		}

		//-----------------------------------------------------------------------------
		public SccErrors Diff(IntPtr hwnd, string filename, SccDiffFlags flags)
		{
			string local_f;
			if (!GetRelativePath(filename, out local_f))
				return SccErrors.InvalidFilePath;

			switch(flags)
			{
				case SccDiffFlags.QdCheckSum:
				case SccDiffFlags.QdContents:
				case SccDiffFlags.QdTime:
				case SccDiffFlags.QuickDiff:
					{
						bool is_different;
						if (!hg_client.DiffSilent(local_f, out is_different))
							return SccErrors.NonSpecificError;

						if (is_different)
							return SccErrors.I_FileDiffers;

						return SccErrors.Ok;
					}
				default:
					{
						bool is_different;

						try
						{
							if (!hg_client.Diff(local_f, out is_different))
								return SccErrors.NonSpecificError;
						}
						catch (HgDiffException)
						{
							Util.HandleHgDiffException();
							return SccErrors.I_OperationCanceled;
						}

						if (!is_different)
						{
							System.Windows.Forms.MessageBox.Show("File: " + filename + " is up to date", "Diff");
							return SccErrors.Ok;
						}

						return SccErrors.Ok;
					}
			}
		}

		//-----------------------------------------------------------------------------
		public SccErrors Remove(IntPtr hwnd, IEnumerable<string> files)
		{
			// TODO: Check if project is opened
			var remove_files = new List<string>();

			foreach (var file in files)
			{
				string f;
				if (!GetRelativePath(file, out f))
					return SccErrors.InvalidFilePath;

				remove_files.Add(f);
			}

			if (remove_files.Count > 0)
			{
				if (!hg_client.Remove(remove_files))
					return SccErrors.OpNotPerformed;
			}

			return SccErrors.Ok;
		}

		//-----------------------------------------------------------------------------
		public SccErrors Rename(IntPtr hwnd, string file, string new_file)
		{
			string f;
			string new_f;

			if (	!GetRelativePath(file, out f)
				||	!GetRelativePath(new_file, out new_f))
			{
				Logger.WriteLine("Can't get relative path: " + file + ", " + new_file);
				return SccErrors.InvalidFilePath;
			}

			if (!hg_client.Rename(f, new_f))
				return SccErrors.NonSpecificError;

			return SccErrors.Ok;
		}

		//-----------------------------------------------------------------------------
		public SccErrors GetExtendedCapabilities(SccExCaps cap, out bool is_supported)
		{
			switch(cap)
			{
				case SccExCaps.DeleteCheckedOut:
				case SccExCaps.RenameCheckedOut:
					{
						is_supported = true;
						break;
					}
				default:
					{
						is_supported = false;
						break;
					}
			}

			return SccErrors.Ok;
		}

		//-----------------------------------------------------------------------------
		public void Dispose()
		{
			if (hg_client != null)
			{
				hg_client.Dispose();
				hg_client = null;
			}
		}
	}
}
