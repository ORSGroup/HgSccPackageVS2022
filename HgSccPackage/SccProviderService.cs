//=========================================================================
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
using System.ComponentModel;
using System.IO;
using System.Diagnostics;
using System.Collections;
using System.Collections.Generic;
using System.Globalization;
using System.Runtime.InteropServices;
using System.Threading;
using HgSccHelper;
using Microsoft.VisualStudio.OLE.Interop;
using Microsoft.VisualStudio.Shell;
using Microsoft.VisualStudio.Shell.Interop;
using Microsoft.VisualStudio;
using System.Windows.Forms;
using HgSccPackage.Vs;
using System.Drawing;
using HgSccPackage.UI;
using System.Linq;
using Timer = System.Windows.Forms.Timer;

namespace HgSccPackage
{
	[Guid("A7F26CA1-1000-4729-896E-0BBE9E380635")]
	public class SccProviderService : 
		IVsSccProvider,             // Required for provider registration with source control manager
		IVsSccManager2,             // Base source control functionality interface
		IVsSccManagerTooltip,       // Provide tooltips for source control items
		IVsSolutionEvents,          // We'll register for solution events, these are useful for source control
		IVsSolutionEvents2,
		IVsQueryEditQuerySave2,     // Required to allow editing of controlled files 
		IVsTrackProjectDocumentsEvents2,  // Useful to track project changes (add, renames, deletes, etc)
		IVsTrackProjectDocumentsEvents3,
		IVsSccGlyphs,
		IDisposable 
	{
		// Whether the provider is active or not
		private bool _active = false;
		// The service and source control provider
		private SccProvider _sccProvider = null;
		// The cookie for solution events 
		private uint _vsSolutionEventsCookie;
		// The cookie for project document events
		private uint _tpdTrackProjectDocumentsCookie;
		// The list of controlled projects hierarchies

		public const string SccProjectName = "<Project Location In Database>";
		public const string SccAuxPath = "<Source Control Database>";
		public const string SccLocalPath = "<Local Binding Root of Project>";

		private readonly HashSet<IVsHierarchy> all_projects = new HashSet<IVsHierarchy>();

		private readonly List<SccProviderStorage> storage_list = new List<SccProviderStorage>();
		private readonly Dictionary<IVsHierarchy, SccProviderStorage> project_to_storage_map = new Dictionary<IVsHierarchy,SccProviderStorage>();
		private readonly HashSet<IVsHierarchy> website_projects = new HashSet<IVsHierarchy>();
		private readonly HashSet<IVsHierarchy> projects_with_scc_bindings = new HashSet<IVsHierarchy>();

		// The list of controlled and offline projects hierarchies
		private readonly HashSet<IVsHierarchy> _offlineProjects = new HashSet<IVsHierarchy>();
		// Variable tracking whether the currently loading solution is controlled (during solution load or merge)
		private string _loadingControlledSolutionLocation = "";
		// The location of the currently controlled solution
		private string _solutionLocation;
		private VsRunningDocumentTable Rdt { get; set; }

		private readonly Dictionary<string, string> add_origin = new Dictionary<string, string>();
		private readonly HashSet<string> outside_projects = new HashSet<string>();

		// Remember the base index where our custom scc glyph start
		private uint customSccGlyphBaseIndex = 0;
		// Our custom image list
		ImageList customSccGlyphsImageList;

		System.Windows.Forms.Timer rdt_timer;
		Dictionary<SccProviderStorage, HashSet<string>> rdt_files_to_update;

		private Dictionary<SccProviderStorage, HashSet<string>> pending_remove;
		private Dictionary<SccProviderStorage, HashSet<string>> pending_delete;
		private Dictionary<SccProviderStorage, List<HgFileInfo>> pending_status;
		private bool pending_save_all_dirty;

		private BackgroundWorker pending_status_updater;
		private object rdt_files_lock = new object();
		private object storage_removal_lock = new object();

		// Indexes of icons in our custom image list
		// NOTE: Only four custom glyphs allowed
		enum CustomSccGlyphs
		{
			Added = 0,
			Deleted = 1,
			Copied = 2,
			Reserved = 3
		};


		#region SccProvider Service initialization/unitialization

		public SccProviderService(SccProvider sccProvider)
		{
			Debug.Assert(null != sccProvider);
			_sccProvider = sccProvider;
		}

		//------------------------------------------------------------------
		public void Dispose()
		{
			Deinit();
		}

		//------------------------------------------------------------------
		void Init()
		{
			Logger.WriteLine("Init");

			// Subscribe to solution events
			var sol = (IVsSolution)_sccProvider.GetService(typeof(SVsSolution));
			sol.AdviseSolutionEvents(this, out _vsSolutionEventsCookie);
			Debug.Assert(VSConstants.VSCOOKIE_NIL != _vsSolutionEventsCookie);

			// Subscribe to project documents
			var tpdService = (IVsTrackProjectDocuments2)_sccProvider.GetService(typeof(SVsTrackProjectDocuments));
			tpdService.AdviseTrackProjectDocumentsEvents(this, out _tpdTrackProjectDocumentsCookie);
			Debug.Assert(VSConstants.VSCOOKIE_NIL != _tpdTrackProjectDocumentsCookie);

			// Get RDT service 

			Rdt = new VsRunningDocumentTable((IVsRunningDocumentTable)_sccProvider.GetService(typeof(SVsRunningDocumentTable)));

			Rdt.AfterAttributeChangeEvent += Rdt_AfterAttributeChangeEvent;
			Rdt.AfterSaveEvent += Rdt_AfterSaveEvent;

			rdt_timer = new Timer();
			rdt_timer.Interval = 300;
			rdt_timer.Tick += new EventHandler(rdt_timer_Tick);

			rdt_files_to_update = new Dictionary<SccProviderStorage, HashSet<string>>();

			pending_delete = new Dictionary<SccProviderStorage, HashSet<string>>();
			pending_remove = new Dictionary<SccProviderStorage, HashSet<string>>();
			pending_status = new Dictionary<SccProviderStorage, List<HgFileInfo>>();
			pending_save_all_dirty = false;

			pending_status_updater = new BackgroundWorker();
			pending_status_updater.DoWork += pending_status_updater_DoWork;
			pending_status_updater.RunWorkerCompleted += pending_status_updater_RunWorkerCompleted;
		}

		//------------------------------------------------------------------
		void RunStatusUpdater()
		{
			lock (rdt_files_lock)
			{
				UpdateStatusParams p = null;

				if (pending_status_updater.IsBusy)
				{
					Logger.WriteLine("Busy");
					return;
				}

				if (rdt_files_to_update.Count != 0)
				{
					var storage = rdt_files_to_update.Keys.First();
					var files = rdt_files_to_update[storage].ToArray();
					rdt_files_to_update.Remove(storage);

					p = new UpdateStatusParams
					{
						Storage = storage,
						Files = files
					};
				}

				if (p != null)
				{
					Logger.WriteLine("RunStatusUpdater: {0}", Thread.CurrentThread.ManagedThreadId);
					pending_status_updater.RunWorkerAsync(p);
				}
			}
		}

		//------------------------------------------------------------------
		void pending_status_updater_RunWorkerCompleted(object sender, RunWorkerCompletedEventArgs e)
		{
			Logger.WriteLine("PendingStatus completed");

			if (e.Cancelled)
				return;

			var result = e.Result as UpdateStatusResults;
			
			if (result != null)
			{
				lock (rdt_files_lock)
				{
					List<HgFileInfo> files_to_update;
					if (!pending_status.TryGetValue(result.Storage, out files_to_update))
					{
						files_to_update = new List<HgFileInfo>();
						pending_status[result.Storage] = files_to_update;
					}

					files_to_update.AddRange(result.FilesInfo);
				}

				QueuePendingCommand(CommandId.icmdPendingTask);
			}
		}

		//------------------------------------------------------------------
		void pending_status_updater_DoWork(object sender, DoWorkEventArgs e)
		{
			var p = (UpdateStatusParams)e.Argument;

			lock (storage_removal_lock)
			{
				// FIXME: Need a better way to synchronize lifetime and execution

				if (!p.Storage.IsValid)
				{
					e.Result = null;
					return;
				}

				var result = p.Storage.GetStatus(p.Files);

				e.Result = new UpdateStatusResults
				{
					Storage = p.Storage,
					FilesInfo = result
				};
			}
		}

		//------------------------------------------------------------------
		void Deinit()
		{
			Logger.WriteLine("Deinit");

			// Unregister from receiving solution events
			if (VSConstants.VSCOOKIE_NIL != _vsSolutionEventsCookie)
			{
				var sol = (IVsSolution)_sccProvider.GetService(typeof(SVsSolution));
				sol.UnadviseSolutionEvents(_vsSolutionEventsCookie);
				_vsSolutionEventsCookie = VSConstants.VSCOOKIE_NIL;
			}

			// Unregister from receiving project documents
			if (VSConstants.VSCOOKIE_NIL != _tpdTrackProjectDocumentsCookie)
			{
				var tpdService = (IVsTrackProjectDocuments2)_sccProvider.GetService(typeof(SVsTrackProjectDocuments));
				tpdService.UnadviseTrackProjectDocumentsEvents(_tpdTrackProjectDocumentsCookie);
				_tpdTrackProjectDocumentsCookie = VSConstants.VSCOOKIE_NIL;
			}

			if (Rdt != null)
			{
				Rdt.AfterAttributeChangeEvent -= Rdt_AfterAttributeChangeEvent;
				Rdt.AfterSaveEvent -= Rdt_AfterSaveEvent;

				Rdt.Dispose();
				Rdt = null;
			}

			if (rdt_timer != null)
			{
				rdt_timer.Tick -= rdt_timer_Tick;
				rdt_timer.Dispose();
			}

			lock (storage_removal_lock)
			{
				foreach (var storage in storage_list)
				{
					storage.UpdateEvent -= UpdateEvent_Handler;
					storage.Close();
				}
			}

			storage_list.Clear();
			if (pending_delete != null)
				pending_delete.Clear();

			if (pending_remove != null)
				pending_remove.Clear();

			if (pending_status != null)
				pending_status.Clear();

			outside_projects.Clear();
			pending_save_all_dirty = false;
		}

		#endregion

		//--------------------------------------------------------------------------------
		// IVsSccProvider specific functions
		//--------------------------------------------------------------------------------
		#region IVsSccProvider interface functions

		// Called by the scc manager when the provider is activated. 
		// Make visible and enable if necessary scc related menu commands
		public int SetActive()
		{
			Logger.WriteLine("Provider set active");
			Logger.WriteLine("sln = '{0}'", _sccProvider.GetSolutionFileName());

			var required_version = new HgVersionInfo {Release = 2, Major = 1, Minor = 1};
			if (!HgVersionChecker.CheckVersion(required_version))
				return VSConstants.E_FAIL;

			_active = true;
			_sccProvider.OnActiveStateChange();

			Init();

			if (!String.IsNullOrEmpty(_sccProvider.GetSolutionFileName()))
			{
				Logger.WriteLine("Manual switch to active");

				ManualyRegisterProjects();

				Logger.WriteLine("Queueing pending status update");
				QueuePendingCommand(CommandId.icmdRefreshStatus);
			}

			return VSConstants.S_OK;
		}

		//------------------------------------------------------------------
		public void HandlePendingCommand()
		{
			Logger.WriteLine("+_+ HandlePendingCommand started");

			if (pending_remove.Count != 0)
			{
				Logger.WriteLine("[pending remove]");

				foreach (var s in pending_remove.Keys)
					s.RemoveFiles(pending_remove[s]);

				pending_remove.Clear();
			}

			if (pending_delete.Count != 0)
			{
				Logger.WriteLine("[pending delete]");

				foreach (var s in pending_delete.Keys)
				{
					var deleted_files = new List<string>();
					foreach (var file in pending_delete[s])
					{
						if (!File.Exists(file))
						{
							Logger.WriteLine("Pending delete: {0}", file);
							deleted_files.Add(file);
						}
					}

					if (deleted_files.Count > 0)
					{
						s.RemoveFiles(deleted_files);
					}
				}

				pending_delete.Clear();
			}

			if (pending_save_all_dirty)
			{
				Logger.WriteLine("[pending save all dirty]");

				pending_save_all_dirty = false;
				_sccProvider.SaveAllIfDirty();
			}

			if (pending_status.Count != 0)
			{
				Logger.WriteLine("[pending status]");

				var nodes = new List<VSITEMSELECTION>();

				lock(rdt_files_lock)
				{
					foreach (var storage in pending_status.Keys)
					{
						var files = pending_status[storage];

						if (storage.IsValid && Active)
						{
							storage.SetCacheStatus(files);
							foreach (var file in files)
							{
								nodes.AddRange(GetControlledProjectsContainingFile(file.File));
							}
						}
					}

					pending_status.Clear();
				}

				if (nodes.Count > 0)
					_sccProvider.RefreshNodesGlyphs(nodes);
			}

			RunStatusUpdater();
			Logger.WriteLine("+_+ HandlePendingCommand ended");
		}

		//-----------------------------------------------------------------------------
		void QueueSaveAllIfDirty()
		{
			if (pending_save_all_dirty)
				return;

			pending_save_all_dirty = true;
			QueuePendingCommand(CommandId.icmdPendingTask);
		}

		//-----------------------------------------------------------------------------
		void QueuePendingRemove(SccProviderStorage storage, string file)
		{
			QueuePendingRemove(storage, new []{file});
		}

		//-----------------------------------------------------------------------------
		void QueuePendingRemove(SccProviderStorage storage, IEnumerable<string> files)
		{
			bool need_queue = pending_remove.Count == 0;

			HashSet<string> files_to_remove;
			if (!pending_remove.TryGetValue(storage, out files_to_remove))
			{
				files_to_remove = new HashSet<string>();
				pending_remove[storage] = files_to_remove;
			}

			foreach (var file in files)
				files_to_remove.Add(file);

			if (need_queue)
				QueuePendingCommand(CommandId.icmdPendingTask);
		}

		//-----------------------------------------------------------------------------
		void QueuePendingDelete(SccProviderStorage storage, string file)
		{
			QueuePendingDelete(storage, new[] { file });
		}

		//-----------------------------------------------------------------------------
		void QueuePendingDelete(SccProviderStorage storage, IEnumerable<string> files)
		{
			bool need_queue = pending_delete.Count == 0;

			HashSet<string> files_to_delete;
			if (!pending_delete.TryGetValue(storage, out files_to_delete))
			{
				files_to_delete = new HashSet<string>();
				pending_delete[storage] = files_to_delete;
			}

			foreach (var file in files)
				files_to_delete.Add(file);

			if (need_queue)
				QueuePendingCommand(CommandId.icmdPendingTask);
		}

		//------------------------------------------------------------------
		private bool QueuePendingCommand(int cmd_id)
		{
			var shell = _sccProvider.GetService<IVsUIShell>();
			if (shell == null)
				return false;

			Guid cmd_set = GuidList.guidSccProviderCmdSet;
			object param = new object();
			var result = shell.PostExecCommand(ref cmd_set,
								  unchecked((uint)cmd_id), (uint)OLECMDEXECOPT.OLECMDEXECOPT_DODEFAULT, ref param);

			return result == VSConstants.S_OK;
		}

		// Called by the scc manager when the provider is deactivated. 
		// Hides and disable scc related menu commands
		public int SetInactive()
		{
			Logger.WriteLine("Provider set inactive");

			Deinit();

			_active = false;
			_sccProvider.OnActiveStateChange();

			return VSConstants.S_OK;
		}

		public int AnyItemsUnderSourceControl(out int pfResult)
		{
			if (!_active)
			{
				pfResult = 0;
			}
			else
			{
				// Although the parameter is an int, it's in reality a BOOL value, so let's return 0/1 values
				pfResult = (project_to_storage_map.Count != 0) ? 1 : 0;
			}
	
			return VSConstants.S_OK;
		}

		#endregion

		//--------------------------------------------------------------------------------
		// IVsSccManager2 specific functions
		//--------------------------------------------------------------------------------
		#region IVsSccManager2 interface functions

		public int BrowseForProject(out string pbstrDirectory, out int pfOK)
		{
			// Obsolete method
			pbstrDirectory = null;
			pfOK = 0;
			return VSConstants.E_NOTIMPL;
		}

		public int CancelAfterBrowseForProject() 
		{
			// Obsolete method
			return VSConstants.E_NOTIMPL;
		}

		/// <summary>
		/// Returns whether the source control provider is fully installed
		/// </summary>
		public int IsInstalled(out int pbInstalled)
		{
			// All source control packages should always return S_OK and set pbInstalled to nonzero
			pbInstalled = 1;
			return VSConstants.S_OK;
		}

		//------------------------------------------------------------------
		IVsPersistDocData GetDocData(string filename)
		{
			var doc_info = Rdt.FindAndLockDocument(filename, _VSRDTFLAGS.RDT_NoLock);
			if (doc_info == null || doc_info.DocData == IntPtr.Zero)
				return null;

			return Marshal.GetObjectForIUnknown(doc_info.DocData) as IVsPersistDocData;
		}

		//------------------------------------------------------------------
		bool IsDirty(string filename)
		{
			var doc_data = GetDocData(filename);
			if (doc_data == null)
				return false;

			int dirty = 0;
			var error = doc_data.IsDocDataDirty(out dirty);
			if (error != VSConstants.S_OK)
				return false;

			return dirty != 0;
		}

		//-----------------------------------------------------------------------------
		private VsStateIcon GetCustomVsIcon(CustomSccGlyphs glyph)
		{
			return (VsStateIcon)(customSccGlyphBaseIndex + (uint)glyph);
		}

		/// <summary>
		/// Provide source control icons for the specified files and returns scc status of files
		/// </summary>
		/// <returns>The method returns S_OK if at least one of the files is controlled, S_FALSE if none of them are</returns>
		public int GetSccGlyph([InAttribute] int cFiles, [InAttribute] string[] rgpszFullPaths, [OutAttribute] VsStateIcon[] rgsiGlyphs, [OutAttribute] uint[] rgdwSccStatus)
		{
//			Debug.Assert(cFiles == 1, "Only getting one file icon at a time is supported");
			SourceControlStatus[] statuses = new SourceControlStatus[rgpszFullPaths.Length];
			GetStatusForFiles(rgpszFullPaths, statuses);

			//Iterate through all the files
			for (int iFile = 0; iFile < cFiles; iFile++)
			{
				// Return the icons and the status. While the status is a combination a flags, we'll return just values 
				// with one bit set, to make life easier for GetSccGlyphsFromStatus
				SourceControlStatus status = statuses[iFile];
				Logger.WriteLine(".File: {0}", rgpszFullPaths[iFile]);

				switch (status)
				{
					case SourceControlStatus.scsAdded:
						{
							rgsiGlyphs[iFile] = GetCustomVsIcon(CustomSccGlyphs.Added);
							if (rgdwSccStatus != null)
								rgdwSccStatus[iFile] = (uint)__SccStatus.SCC_STATUS_CHECKEDOUT;
							break;
						}
					case SourceControlStatus.scsCopied:
						{
							rgsiGlyphs[iFile] = GetCustomVsIcon(CustomSccGlyphs.Copied);
							if (rgdwSccStatus != null)
								rgdwSccStatus[iFile] = (uint)__SccStatus.SCC_STATUS_CHECKEDOUT;
							break;
						}
					case SourceControlStatus.scsDeleted:
					case SourceControlStatus.scsRemoved:
						{
							rgsiGlyphs[iFile] = GetCustomVsIcon(CustomSccGlyphs.Deleted);
							if (rgdwSccStatus != null)
								rgdwSccStatus[iFile] = (uint)__SccStatus.SCC_STATUS_DELETED;
							break;
						}
					case SourceControlStatus.scsIgnored:
						{
							rgsiGlyphs[iFile] = VsStateIcon.STATEICON_EXCLUDEDFROMSCC;
							if (rgdwSccStatus != null)
								rgdwSccStatus[iFile] = (uint)__SccStatus.SCC_STATUS_NOTCONTROLLED;
							break;
						}
					case SourceControlStatus.scsClean:
						{
							rgsiGlyphs[iFile] = VsStateIcon.STATEICON_CHECKEDIN;
							if (rgdwSccStatus != null)
								rgdwSccStatus[iFile] = (uint)__SccStatus.SCC_STATUS_CONTROLLED;
							break;
						}
					case SourceControlStatus.scsModified:
						{
							rgsiGlyphs[iFile] = VsStateIcon.STATEICON_CHECKEDOUT;
							if (rgdwSccStatus != null)
								rgdwSccStatus[iFile] = (uint)__SccStatus.SCC_STATUS_CHECKEDOUT;
							break;
						}
					default:
						//System.Collections.Generic.IList<VSITEMSELECTION> nodes = GetControlledProjectsContainingFile(rgpszFullPaths[i]);
						/*
											if (nodes.Count > 0)
											{
												// If the file is not controlled, but is member of a controlled project, report the item as checked out (same as source control in VS2003 did)
												// If the provider wants to have special icons for "pending add" files, the IVsSccGlyphs interface needs to be supported
												rgsiGlyphs[0] = VsStateIcon.STATEICON_CHECKEDOUT;
												if (rgdwSccStatus != null)
												{
													rgdwSccStatus[0] = (uint) __SccStatus.SCC_STATUS_CHECKEDOUT;
												}
											}
											else
						*/
						{
							if (outside_projects.Contains(rgpszFullPaths[iFile]))
							{
								rgsiGlyphs[iFile] = VsStateIcon.STATEICON_EXCLUDEDFROMSCC;
								if (rgdwSccStatus != null)
								{
									rgdwSccStatus[iFile] = (uint)__SccStatus.SCC_STATUS_CONTROLLED;
								}
							}
							else
							{
								// This is an uncontrolled file, return a blank scc glyph for it
								rgsiGlyphs[iFile] = VsStateIcon.STATEICON_BLANK;
								if (rgdwSccStatus != null)
								{
									rgdwSccStatus[iFile] = (uint)__SccStatus.SCC_STATUS_NOTCONTROLLED;
								}
							}
						}
						break;
				}

				if (status != SourceControlStatus.scsUncontrolled)
				{
					if (IsDirty(rgpszFullPaths[iFile]))
						rgsiGlyphs[iFile] = VsStateIcon.STATEICON_EDITABLE;
				}
			}

			return VSConstants.S_OK;
		}

		/// <summary>
		/// Determines the corresponding scc status glyph to display, given a combination of scc status flags
		/// </summary>
		public int GetSccGlyphFromStatus([InAttribute] uint dwSccStatus, [OutAttribute] VsStateIcon[] psiGlyph)
		{
			switch (dwSccStatus)
			{
				case (uint) __SccStatus.SCC_STATUS_CHECKEDOUT:
					psiGlyph[0] = VsStateIcon.STATEICON_CHECKEDOUT;
					break;
				case (uint) __SccStatus.SCC_STATUS_CONTROLLED:
					psiGlyph[0] = VsStateIcon.STATEICON_CHECKEDIN;
					break;
				default:
					psiGlyph[0] = VsStateIcon.STATEICON_BLANK;
					break;
			}
			return VSConstants.S_OK;
		}

		public uint SourceStatusToSccStatus(SourceControlStatus status)
		{
			switch (status)
			{
				case SourceControlStatus.scsAdded:
				case SourceControlStatus.scsModified:
				case SourceControlStatus.scsCopied:
					return (uint)__SccStatus.SCC_STATUS_CHECKEDOUT;
				case SourceControlStatus.scsClean:
					return (uint) __SccStatus.SCC_STATUS_CONTROLLED;
				case SourceControlStatus.scsIgnored:
					return (uint) __SccStatus.SCC_STATUS_CONTROLLED;
				case SourceControlStatus.scsDeleted:
				case SourceControlStatus.scsRemoved:
					return (uint) __SccStatus.SCC_STATUS_DELETED;
				case SourceControlStatus.scsUncontrolled:
					return (uint) __SccStatus.SCC_STATUS_NOTCONTROLLED;
			}

			return (uint)__SccStatus.SCC_STATUS_NOTCONTROLLED;
		}

		//------------------------------------------------------------------
		SccProviderStorage GetStorageForFile(string filename)
		{
			foreach (var storage in storage_list)
			{
				if (storage.IsStorageControlled(filename))
					return storage;
			}

			return null;
		}

		//-----------------------------------------------------------------
		SccProviderStorage GetStorageParentForFile(string filename)
		{
			foreach (var storage in storage_list)
			{
				if (storage.IsPathUnderRoot(filename) && !storage.IsStorageControlled(filename))
					return storage;
			}

			return null;
		}

		//------------------------------------------------------------------
		SccProviderStorage GetStorageForProject(IVsHierarchy hierarchy)
		{
			if (hierarchy == null)
			{
				// this is solution, get the solution hierarchy
				hierarchy = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));
			}

			if (hierarchy == null)
				return null;

			SccProviderStorage storage;
			if (project_to_storage_map.TryGetValue(hierarchy, out storage))
				return storage;

			return null;
		}

		/// <summary>
		/// One of the most important methods in a source control provider, is called by projects that are under source control when they are first opened to register project settings
		/// </summary>
		public int RegisterSccProject([InAttribute] IVsSccProject2 pscp2Project, [InAttribute] string pszSccProjectName, [InAttribute] string pszSccAuxPath, [InAttribute] string pszSccLocalPath, [InAttribute] string pszProvider)
		{
			if (pszProvider.CompareTo(_sccProvider.ProviderName)!=0)
			{
				// If the provider name controlling this project is not our provider, the user may be adding to a 
				// solution controlled by this provider an existing project controlled by some other provider.
				// We'll deny the registration with scc in such case.
				return VSConstants.E_FAIL;
			}

			Logger.WriteLine("RegisterSccProject: sln = '{0}'", _sccProvider.GetSolutionFileName());

			if (pscp2Project == null)
			{
				string solutionFile = _sccProvider.GetSolutionFileName();
				if (string.IsNullOrEmpty(solutionFile) || !File.Exists(solutionFile))
					return VSConstants.E_FAIL;

//				Logger.WriteLine("RegisterSccProject: adding solution");
				// Manual registration with source control of the solution, from OnAfterOpenSolution
				Logger.WriteLine("Solution {0} is registering with source control - {1}, {2}, {3}, {4}", _sccProvider.GetSolutionFileName(), pszSccProjectName, pszSccAuxPath, pszSccLocalPath, pszProvider);

				var solHier = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));

				var work_dir = Path.GetDirectoryName(solutionFile);
				var found_storage = GetStorageForFile(solutionFile);
				var storage = found_storage;
				
				if (storage == null)
					storage = new SccProviderStorage();

				// FIXME: Проверить что путь у солюшена выше по иерархии чем у проекта
				// а также что у проекта нет репозитория
				if (!storage.IsValid)
				{
					var err = storage.Init(work_dir, SccOpenProjectFlags.None);
					if (err != SccErrors.Ok)
						return VSConstants.E_FAIL;
				}

				if (storage.GetFileStatus(solutionFile) == SourceControlStatus.scsUncontrolled)
					outside_projects.Add(solutionFile);

				project_to_storage_map[solHier] = storage;
				if (found_storage == null)
				{
					storage.UpdateEvent += UpdateEvent_Handler;
					storage_list.Add(storage);
				}
			}
			else
			{
				Logger.WriteLine("Project {0} is registering with source control - {1}, {2}, {3}, {4}", _sccProvider.GetProjectFileName(pscp2Project), pszSccProjectName, pszSccAuxPath, pszSccLocalPath, pszProvider);

				// Add the project to the list of controlled projects
				var hierProject = (IVsHierarchy)pscp2Project;
				if (!project_to_storage_map.ContainsKey(hierProject))
				{
					var project_path = _sccProvider.GetProjectFileName(pscp2Project);
					var work_dir = Path.GetDirectoryName(project_path);

//					Logger.WriteLine("RegisterSccProject: adding project = '{0}'", project_path);

					var found_storage = GetStorageForFile(project_path);
					var storage = found_storage;

					if (storage == null)
						storage = new SccProviderStorage();

					if (!storage.IsValid)
					{
						var err = storage.Init(work_dir, SccOpenProjectFlags.None);
						if (err != SccErrors.Ok)
							return VSConstants.E_FAIL;

						var parent = GetStorageParentForFile(project_path);
						if (parent != null) //means that this is a sub repo
						{
							parent.AddSubrepoStorage(work_dir, storage);
						}
					}

					if (storage.GetFileStatus(project_path) == SourceControlStatus.scsUncontrolled)
						outside_projects.Add(project_path);

					if (Directory.Exists(project_path))
						website_projects.Add(hierProject);

					project_to_storage_map[hierProject] = storage;
					if (found_storage == null)
					{
						storage.UpdateEvent += UpdateEvent_Handler;
						storage_list.Add(storage);
					}
				}

				if (project_to_storage_map.ContainsKey(hierProject))
				{
					if (pszSccProjectName != "" && pszSccAuxPath != "" && pszSccLocalPath != "")
						projects_with_scc_bindings.Add(hierProject);
				}
			}

			return VSConstants.S_OK;
		}

		/// <summary>
		/// Called by projects registered with the source control portion of the environment before they are closed. 
		/// </summary>
		public int UnregisterSccProject([InAttribute] IVsSccProject2 pscp2Project)
		{
			// Get the project's hierarchy
			IVsHierarchy hierProject = null;
			if (pscp2Project == null)
			{
				// If the project's pointer is null, it must be the solution calling to unregister, from OnBeforeCloseSolution
				Logger.WriteLine("Solution {0} is unregistering with source control.", _sccProvider.GetSolutionFileName());
				hierProject = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));
			}
			else
			{
				Logger.WriteLine("Project {0} is unregistering with source control.", _sccProvider.GetProjectFileName(pscp2Project));
				hierProject = (IVsHierarchy)pscp2Project;
			}

			// Remove the project from the list of controlled projects
			lock (storage_removal_lock)
			{
				if (project_to_storage_map.ContainsKey(hierProject))
				{
					var storage = project_to_storage_map[hierProject];
					project_to_storage_map.Remove(hierProject);

					if (!project_to_storage_map.ContainsValue(storage))
					{
						storage.UpdateEvent -= UpdateEvent_Handler;
						storage_list.Remove(storage);
						storage.Close();
					}

					projects_with_scc_bindings.Remove(hierProject);
					website_projects.Remove(hierProject);

					if (pscp2Project == null)
						outside_projects.Remove(_sccProvider.GetSolutionFileName());
					else
						outside_projects.Remove(_sccProvider.GetProjectFileName(pscp2Project));

					return VSConstants.S_OK;
				}
			}
			
			return VSConstants.S_FALSE;
		}

		#endregion

		//--------------------------------------------------------------------------------
		// IVsSccManagerTooltip specific functions
		//--------------------------------------------------------------------------------
		#region IVsSccManagerTooltip interface functions

		/// <summary>
		/// Called by solution explorer to provide tooltips for items. Returns a text describing the source control status of the item.
		/// </summary>
		public int GetGlyphTipText([InAttribute] IVsHierarchy phierHierarchy, [InAttribute] uint itemidNode, out string pbstrTooltipText)
		{
			// Initialize output parameters
			pbstrTooltipText = "";

			System.Collections.Generic.IList<string> files = _sccProvider.GetNodeFiles(phierHierarchy, itemidNode);
			if (files.Count == 0)
			{
				return VSConstants.S_OK;
			}

			// Return the glyph text based on the first file of node (the master file)
			SourceControlStatus status = GetFileStatus(files[0]);
			switch (status)
			{
				case SourceControlStatus.scsAdded:
					pbstrTooltipText = "Added";
					break;
				case SourceControlStatus.scsCopied:
					pbstrTooltipText = "Copied from other file";
					break;
				case SourceControlStatus.scsDeleted:
					pbstrTooltipText = "Deleted";
					break;
				case SourceControlStatus.scsRemoved:
					pbstrTooltipText = "Removed";
					break;
				case SourceControlStatus.scsIgnored:
					pbstrTooltipText = "Ignored";
					break;
				case SourceControlStatus.scsClean:
					pbstrTooltipText = "Clean"; 
					break;
				case SourceControlStatus.scsModified:
					pbstrTooltipText = "Modified";
					break;
				default:
					// If the file is not controlled, but is member of a controlled project, report the item as checked out (same as source control in VS2003 did)
					// If the provider wants to have special icons for "pending add" files, the IVsSccGlyphs interface needs to be supported
					System.Collections.Generic.IList<VSITEMSELECTION> nodes = GetControlledProjectsContainingFile(files[0]);
					if (nodes.Count > 0)
					{
//						pbstrTooltipText = Resources.ResourceManager.GetString("Status_PendingAdd");
						pbstrTooltipText = Resources.ResourceManager.GetString("Status_Uncontrolled");
					}
					break;
			}

			return VSConstants.S_OK;
		}

		#endregion

		//--------------------------------------------------------------------------------
		// IVsSolutionEvents and IVsSolutionEvents2 specific functions
		//--------------------------------------------------------------------------------
		#region IVsSolutionEvents interface functions

		public int OnAfterCloseSolution([InAttribute] Object pUnkReserved)
		{
			// Reset all source-control-related data now that solution is closed
			project_to_storage_map.Clear();
			website_projects.Clear();
			all_projects.Clear();
			_offlineProjects.Clear();
			_sccProvider.SolutionHasDirtyProps = false;
			_loadingControlledSolutionLocation = "";
			_solutionLocation = "";
			projects_with_scc_bindings.Clear();

			lock (storage_removal_lock)
			{
				foreach (var storage in storage_list)
				{
					storage.UpdateEvent -= UpdateEvent_Handler;
					storage.Close();
				}
			}

			storage_list.Clear();
			_sccProvider.SolutionHaveSccBindings = false;
			outside_projects.Clear();

			return VSConstants.S_OK;
		}

		public int OnAfterLoadProject([InAttribute] IVsHierarchy pStubHierarchy, [InAttribute] IVsHierarchy pRealHierarchy)
		{
			Logger.WriteLine("OnAfterLoadProject: {0}", pRealHierarchy);
			return VSConstants.S_OK;
		}

		public int OnAfterOpenProject([InAttribute] IVsHierarchy pHierarchy, [InAttribute] int fAdded)
		{
			if (!Active)
				return VSConstants.S_OK;

			Logger.WriteLine("OnAfterOpenProject: {0}, added = {1}", pHierarchy, fAdded);

			// If a solution folder is added to the solution after the solution is added to scc, we need to controll that folder
			if (VsSolutionUtil.IsSolutionFolderProject(pHierarchy) && (fAdded == 1))
			{
				var solHier = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));
				if (IsProjectControlled(solHier))
				{
					// Register this solution folder using the same location as the solution
					var pSccProject = (IVsSccProject2)pHierarchy;
					RegisterSccProject(pSccProject, _solutionLocation, "", "", _sccProvider.ProviderName);

					// We'll also need to refresh the solution folders glyphs to reflect the controlled state
					System.Collections.Generic.IList<VSITEMSELECTION> nodes = new List<VSITEMSELECTION>();

					VSITEMSELECTION vsItem;
					vsItem.itemid = VSConstants.VSITEMID_ROOT;
					vsItem.pHier = pHierarchy;
					nodes.Add(vsItem);

					_sccProvider.RefreshNodesGlyphs(nodes);
				}
			}
			else
			{
				var prj = pHierarchy as IVsSccProject2;
				if (prj != null && !IsProjectControlled(pHierarchy))
				{
					RegisterSccProject(prj, "", "", "", _sccProvider.ProviderName);
				}
			}

			all_projects.Add(pHierarchy);

			return VSConstants.S_OK;
		}

		//------------------------------------------------------------------
		void ManualyRegisterProjects()
		{
			Logger.WriteLine("Manualy register projects");

			bool register_scc_projects = HgSccOptions.Instance.CheckProjectsForMercurialRepository;
			if (!register_scc_projects)
			{
				var solution_dir = Path.GetDirectoryName(_sccProvider.GetSolutionFileName());
				var storage = new SccProviderStorage();

				// If solution is not controlled, check if there is
				// a mercurial repository

				if (SccErrors.Ok == storage.Init(solution_dir, SccOpenProjectFlags.None))
				{
					Logger.WriteLine("Solution is not controlled, but there is a mercurial repository");
					register_scc_projects = true;
				}
			}

			if (register_scc_projects)
			{
				RegisterSccProject(null, "", "", "", _sccProvider.ProviderName);

				var solution = _sccProvider.GetService<IVsSolution>();
				var scc_projects = solution.EnumHierarchies().Where(hier => hier is IVsSccProject2);
				foreach (var prj in scc_projects)
				{
					all_projects.Add(prj);
					RegisterSccProject((IVsSccProject2)prj, "", "", "", _sccProvider.ProviderName);
				}

			}

			all_projects.Add((IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution)));
		}

		public int OnAfterOpenSolution([InAttribute] Object pUnkReserved, [InAttribute] int fNewSolution)
		{
			if (!Active)
				return VSConstants.S_OK;

			// This event is fired last by the shell when opening a solution.
			// By this time, we have already loaded the solution persistence data from the PreLoad section
			// the controlled projects should be opened and registered with source control
			bool register_scc_projects = _loadingControlledSolutionLocation.Length > 0;

			if (HgSccOptions.Instance.CheckProjectsForMercurialRepository)
			{
				// If this option is set, then we will check
				// for mercurial repository at the project location
				// even if the solution is not controlled and located
				// outside of mercurial repository

				// One downside, that this check may take quite some time
				// for solution with a lot of projects, that
				// are not in the mercurial repository

				register_scc_projects = true;
			}

			if (!register_scc_projects)
			{
				var solution_dir = Path.GetDirectoryName(_sccProvider.GetSolutionFileName());
				var storage = new SccProviderStorage();

				// If solution is not controlled, check if there is
				// a mercurial repository

				if (SccErrors.Ok == storage.Init(solution_dir, SccOpenProjectFlags.None))
				{
					Logger.WriteLine("Solution is not controlled, but there is a mercurial repository");
					register_scc_projects = true;
				}
			}

			if (register_scc_projects)
			{
				// We'll also need to refresh the solution glyphs to reflect the controlled state
				System.Collections.Generic.IList<VSITEMSELECTION> nodes = new List<VSITEMSELECTION>();

				// If the solution was controlled, now it is time to register the solution hierarchy with souce control, too.
				// Note that solution is not calling RegisterSccProject(), the scc package will do this call as it knows the source control location
				RegisterSccProject(null, _loadingControlledSolutionLocation, "", "", _sccProvider.ProviderName);

				VSITEMSELECTION vsItem;
				vsItem.itemid = VSConstants.VSITEMID_ROOT;
				vsItem.pHier = null;
				nodes.Add(vsItem);

				// Also, solution folders won't call RegisterSccProject, so we have to enumerate them and register them with scc once the solution is controlled
				var solution = (IVsSolution)_sccProvider.GetService(typeof(SVsSolution));
				var solution_folders = solution.EnumHierarchies(VsSolutionUtil.SolutionFolderGuid);

				foreach (IVsHierarchy pHier in solution_folders)
				{
					// Register this solution folder using the same location as the solution
					var pSccProject = pHier as IVsSccProject2;
					if (pSccProject != null)
					{
						RegisterSccProject(pSccProject, _loadingControlledSolutionLocation, "",
										   "", _sccProvider.ProviderName);

						vsItem.itemid = VSConstants.VSITEMID_ROOT;
						vsItem.pHier = pHier;
						nodes.Add(vsItem);
					}
				}

				// Refresh the glyphs now for solution and solution folders
				_sccProvider.RefreshNodesGlyphs(nodes);
			}

			_solutionLocation = _loadingControlledSolutionLocation;

			// reset the flag now that solution open completed
			_loadingControlledSolutionLocation = "";

			all_projects.Add((IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution)));

			return VSConstants.S_OK;
		}

		public int OnBeforeCloseProject([InAttribute] IVsHierarchy pHierarchy, [InAttribute] int fRemoved)
		{
			Logger.WriteLine("OnBeforeCloseProject: {0}", pHierarchy);
			return VSConstants.S_OK;
		}

		public int OnBeforeCloseSolution([InAttribute] Object pUnkReserved)
		{
			// Since we registered the solution with source control from OnAfterOpenSolution, it would be nice to unregister it, too, when it gets closed.
			// Also, unregister the solution folders

			var solution = (IVsSolution)_sccProvider.GetService(typeof(SVsSolution));
			var solution_folders = solution.EnumHierarchies(VsSolutionUtil.SolutionFolderGuid);

			foreach (IVsHierarchy pHier in solution_folders)
			{
				var pSccProject = pHier as IVsSccProject2;
				if (pSccProject != null)
				{
					UnregisterSccProject(pSccProject);
					all_projects.Remove(pHier);
				}
			}

			UnregisterSccProject(null);
			all_projects.Remove((IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution)));
			outside_projects.Clear();

			return VSConstants.S_OK;
		}

		public int OnBeforeUnloadProject([InAttribute] IVsHierarchy pRealHierarchy, [InAttribute] IVsHierarchy pStubHierarchy)
		{
			Logger.WriteLine("OnBeforeUnloadProject: {0}", pRealHierarchy);
			return VSConstants.S_OK;
		}

		public int OnQueryCloseProject([InAttribute] IVsHierarchy pHierarchy, [InAttribute] int fRemoving, [InAttribute] ref int pfCancel)
		{
			return VSConstants.S_OK;
		}

		public int OnQueryCloseSolution([InAttribute] Object pUnkReserved, [InAttribute] ref int pfCancel)
		{
			return VSConstants.S_OK;
		}

		public int OnQueryUnloadProject([InAttribute] IVsHierarchy pRealHierarchy, [InAttribute] ref int pfCancel)
		{
			return VSConstants.S_OK;
		}

		public int OnAfterMergeSolution ([InAttribute] Object pUnkReserved )
		{
			// reset the flag now that solutions were merged and the merged solution completed opening
			_loadingControlledSolutionLocation = "";

			return VSConstants.S_OK;
		}

		#endregion

		//--------------------------------------------------------------------------------
		// IVsQueryEditQuerySave2 specific functions
		//--------------------------------------------------------------------------------
		#region IVsQueryEditQuerySave2 interface functions

		public int BeginQuerySaveBatch ()
		{
			return VSConstants.S_OK;
		}

		public int EndQuerySaveBatch ()
		{
			return VSConstants.S_OK;
		}

		public int DeclareReloadableFile([InAttribute] string pszMkDocument, [InAttribute] uint rgf, [InAttribute] VSQEQS_FILE_ATTRIBUTE_DATA[] pFileInfo)
		{
			return VSConstants.S_OK;
		}

		public int DeclareUnreloadableFile([InAttribute] string pszMkDocument, [InAttribute] uint rgf, [InAttribute] VSQEQS_FILE_ATTRIBUTE_DATA[] pFileInfo)
		{
			return VSConstants.S_OK;
		}

		public int IsReloadable ([InAttribute] string pszMkDocument, out int pbResult )
		{
			// Since we're not tracking which files are reloadable and which not, consider everything reloadable
			pbResult = 1;
			return VSConstants.S_OK;
		}

		public int OnAfterSaveUnreloadableFile([InAttribute] string pszMkDocument, [InAttribute] uint rgf, [InAttribute] VSQEQS_FILE_ATTRIBUTE_DATA[] pFileInfo)
		{
			return VSConstants.S_OK;
		}

		/// <summary>
		/// Called by projects and editors before modifying a file
		/// The function allows the source control systems to take the necessary actions (checkout, flip attributes)
		/// to make the file writable in order to allow the edit to continue
		///
		/// There are a lot of cases to deal with during QueryEdit/QuerySave. 
		/// - called in commmand line mode, when UI cannot be displayed
		/// - called during builds, when save shoudn't probably be allowed
		/// - called during projects migration, when projects are not open and not registered yet with source control
		/// - checking out files may bring new versions from vss database which may be reloaded and the user may lose in-memory changes; some other files may not be reloadable
		/// - not all editors call QueryEdit when they modify the file the first time (buggy editors!), and the files may be already dirty in memory when QueryEdit is called
		/// - files on disk may be modified outside IDE and may have attributes incorrect for their scc status
		/// - checkouts may fail
		/// The sample provider won't deal with all these situations, but a real source control provider should!
		/// </summary>
		public int QueryEditFiles([InAttribute] uint rgfQueryEdit, [InAttribute] int cFiles, [InAttribute] string[] rgpszMkDocuments, [InAttribute] uint[] rgrgf, [InAttribute] VSQEQS_FILE_ATTRIBUTE_DATA[] rgFileInfo, out uint pfEditVerdict, out uint prgfMoreInfo)
		{
			// Initialize output variables
			pfEditVerdict = (uint)tagVSQueryEditResult.QER_EditOK;
			prgfMoreInfo = 0;

			return VSConstants.S_OK;
		}

		/// <summary>
		/// Called by editors and projects before saving the files
		/// The function allows the source control systems to take the necessary actions (checkout, flip attributes)
		/// to make the file writable in order to allow the file saving to continue
		/// </summary>
		public int QuerySaveFile([InAttribute] string pszMkDocument, [InAttribute] uint rgf, [InAttribute] VSQEQS_FILE_ATTRIBUTE_DATA[] pFileInfo, out uint pdwQSResult)
		{
			// Delegate to the other QuerySave function
			string[] rgszDocuements = new string[1];
			uint[] rgrgf = new uint[1];
			rgszDocuements[0] = pszMkDocument;
			rgrgf[0] = rgf;
			return QuerySaveFiles(rgf, 1, rgszDocuements, rgrgf, pFileInfo, out pdwQSResult);
		}

		/// <summary>
		/// Called by editors and projects before saving the files
		/// The function allows the source control systems to take the necessary actions (checkout, flip attributes)
		/// to make the file writable in order to allow the file saving to continue
		/// </summary>
		public int QuerySaveFiles([InAttribute] uint rgfQuerySave, [InAttribute] int cFiles, [InAttribute] string[] rgpszMkDocuments, [InAttribute] uint[] rgrgf, [InAttribute] VSQEQS_FILE_ATTRIBUTE_DATA[] rgFileInfo, out uint pdwQSResult)
		{
//			IVsRunningDocumentTable rdt = (IVsRunningDocumentTable)_sccProvider.GetService(typeof(IVsRunningDocumentTable));

			var checkout_files = new List<string>();

			// Initialize output variables
			// It's a bit unfortunate that we have to return only one set of flags for all the files involved in the operation
			// The last file will win setting this flag
			pdwQSResult = (uint)tagVSQuerySaveResult.QSR_SaveOK;

			// In non-UI mode attempt to silently flip the attributes of files or check them out 
			// and allow the save, because the user cannot be asked what to do with the file
			if (_sccProvider.InCommandLineMode())
			{
				rgfQuerySave = rgfQuerySave | (uint)tagVSQuerySaveFlags.QSF_SilentMode;
			}

			try 
			{
				SourceControlStatus[] statuses = new SourceControlStatus[rgpszMkDocuments.Length];
				GetStatusForFiles(rgpszMkDocuments, statuses);

				for (int iFile = 0; iFile < cFiles; iFile++)
				{
					Logger.WriteLine("QuerySaveFiles: [{0}]: {1}", iFile, rgpszMkDocuments[iFile]);
//					SourceControlStatus status = GetFileStatus(rgpszMkDocuments[iFile]);
					SourceControlStatus status = statuses[iFile];
					bool fileExists = File.Exists(rgpszMkDocuments[iFile]);
					bool isFileReadOnly = false;
					if (fileExists)
					{
						isFileReadOnly = ((File.GetAttributes(rgpszMkDocuments[iFile]) & FileAttributes.ReadOnly) == FileAttributes.ReadOnly);
					}

					switch (status)
					{
						case SourceControlStatus.scsClean:
							{
								if (fileExists && isFileReadOnly)
								{
									// Make the file writable and allow the save
									File.SetAttributes(rgpszMkDocuments[iFile], FileAttributes.Normal);
								}
								// TODO: Add dirty file to checkout_files
//								rdt.GetDocumentInfo()
								checkout_files.Add(rgpszMkDocuments[iFile]);
								// Allow the save now 
								pdwQSResult = (uint)tagVSQuerySaveResult.QSR_SaveOK;
								break;
							}
						case SourceControlStatus.scsModified:	 // fall through
						case SourceControlStatus.scsAdded:
						case SourceControlStatus.scsCopied:
						case SourceControlStatus.scsIgnored:
						case SourceControlStatus.scsDeleted:
						case SourceControlStatus.scsRemoved:
						case SourceControlStatus.scsUncontrolled:
							if (fileExists && isFileReadOnly)
							{
								// Make the file writable and allow the save
								File.SetAttributes(rgpszMkDocuments[iFile], FileAttributes.Normal);
							}
							// Allow the save now 
							pdwQSResult = (uint)tagVSQuerySaveResult.QSR_SaveOK;
							break;
					}
				}
			}
			catch (Exception)
			{
				// If an exception was caught, do not allow the save
				pdwQSResult = (uint)tagVSQuerySaveResult.QSR_NoSave_Cancel;
			}

			// FIXME: Переделать на сохранение только нужных файлов
/*
			var sol = (IVsSolution)_sccProvider.GetService(typeof(SVsSolution));
			sol.SaveSolutionElement((uint)__VSSLNSAVEOPTIONS.SLNSAVEOPT_SaveIfDirty, null, 0);
*/

/*
			IList<VSITEMSELECTION> lst = GetControlledProjectsContainingFiles(checkout_files);
			var sol = (IVsSolution)_sccProvider.GetService(typeof(SVsSolution));

			foreach (var item in lst)
			{
				var proj = item.pHier as IVsProject2;
				if (proj == null)
				{
					// solution
					Logger.WriteLine("QuerySaveFile, solution");
					sol.SaveSolutionElement((uint)__VSSLNSAVEOPTIONS.SLNSAVEOPT_SaveIfDirty, null, 0);
				}
				else
				{
					object obj_doc_cookie;

					var err = item.pHier.GetProperty(item.itemid, (int)__VSHPROPID.VSHPROPID_ItemDocCookie, out obj_doc_cookie);
					if (err != VSConstants.S_OK)
						continue;

					uint doc_cookie = (uint)(int)obj_doc_cookie;

					string doc_path;
					err = proj.GetMkDocument(item.itemid, out doc_path);
					if (err == VSConstants.S_OK)
					{
						sol.SaveSolutionElement((uint) __VSSLNSAVEOPTIONS.SLNSAVEOPT_SaveIfDirty, null, doc_cookie);
					}
				}
			}
*/

/*
			foreach (var file in checkout_files)
			{
				storage.SetCacheStatus(file, SourceControlStatus.scsCheckedOut);
			}
*/

/*
			IList<VSITEMSELECTION> lst = GetControlledProjectsContainingFiles(checkout_files);
			if (lst.Count != 0)
			{
				_sccProvider.RefreshNodesGlyphs(lst);
			}
*/

			return VSConstants.S_OK;
		}

		#endregion

		//--------------------------------------------------------------------------------
		// IVsTrackProjectDocumentsEvents2 specific functions
		//--------------------------------------------------------------------------------
		public int OnQueryAddFiles([InAttribute] IVsProject pProject, [InAttribute] int cFiles, [InAttribute] string[] rgpszMkDocuments, [InAttribute] VSQUERYADDFILEFLAGS[] rgFlags, [OutAttribute] VSQUERYADDFILERESULTS[] pSummaryResult, [OutAttribute] VSQUERYADDFILERESULTS[] rgResults)
		{
			pSummaryResult[0] = VSQUERYADDFILERESULTS.VSQUERYADDFILERESULTS_AddOK;
			if (rgResults != null)
			{
				for (int iFile = 0; iFile < cFiles; iFile++)
				{
					Logger.WriteLine("OnQueryAddFiles: [{0}]: {1}", iFile, rgpszMkDocuments[iFile]);
					rgResults[iFile] = VSQUERYADDFILERESULTS.VSQUERYADDFILERESULTS_AddOK;
				}
			}

			try
			{
				var sccProject = pProject as IVsSccProject2;
				var pHier = pProject as IVsHierarchy;
				string projectName = null;
				if (sccProject == null)
				{
					// This is the solution calling
					pHier = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));
					projectName = _sccProvider.GetSolutionFileName();
				}
				else
				{
					// If the project doesn't support source control, it will be skipped
					if (sccProject != null)
					{
						projectName = _sccProvider.GetProjectFileName(sccProject);
					}
				}

				if (projectName != null)
				{
					for (int iFile = 0; iFile < cFiles; iFile++)
					{
						var storage = GetStorageForProject(pHier);
						if (storage != null)
						{
							SourceControlStatus status = storage.GetFileStatus(rgpszMkDocuments[iFile]);
							if (status != SourceControlStatus.scsUncontrolled)
							{
							}
						}
					}
				}
			}
			catch (Exception)
			{
				pSummaryResult[0] = VSQUERYADDFILERESULTS.VSQUERYADDFILERESULTS_AddNotOK;
				if (rgResults != null)
				{
					for (int iFile = 0; iFile < cFiles; iFile++)
					{
						rgResults[iFile] = VSQUERYADDFILERESULTS.VSQUERYADDFILERESULTS_AddNotOK;
					}
				}
			}

			return VSConstants.S_OK;
		}

		/// <summary>
		/// Implement this function to update the project scc glyphs when the items are added to the project.
		/// If a project doesn't call GetSccGlyphs as they should do (as solution folder do), this will update correctly the glyphs when the project is controled
		/// </summary>
		public int OnAfterAddFilesEx([InAttribute] int cProjects, [InAttribute] int cFiles, [InAttribute] IVsProject[] rgpProjects, [InAttribute] int[] rgFirstIndices, [InAttribute] string[] rgpszMkDocuments, [InAttribute] VSADDFILEFLAGS[] rgFlags)
		{
			var files_map = new Dictionary<SccProviderStorage, List<string>>();
			var copy_files_map = new Dictionary<SccProviderStorage, Dictionary<string, string>>();

			var selected_items = new List<VSITEMSELECTION>();

			// Start by iterating through all projects calling this function
			for (int iProject = 0; iProject < cProjects; iProject++)
			{
				var sccProject = rgpProjects[iProject] as IVsSccProject2;
				var pHier = rgpProjects[iProject] as IVsHierarchy;

				// If the project is not controllable, or is not controlled, skip it
				if (sccProject == null || !IsProjectControlled(pHier))
				{
					continue;
				}

				if (IsWebSiteProject(pHier))
					continue;

				int iProjectFilesStart = rgFirstIndices[iProject];
				int iNextProjecFilesStart = cFiles;
				if (iProject < cProjects - 1)
				{
					iNextProjecFilesStart = rgFirstIndices[iProject + 1];
				}

				var project_storage = GetStorageForProject(pHier);
				if (project_storage == null)
					continue;

				Dictionary<string, string> copy_files;
				if (!copy_files_map.TryGetValue(project_storage, out copy_files))
				{
					copy_files = new Dictionary<string, string>();
					copy_files_map[project_storage] = copy_files;
				}

				List<string> files;
				if (!files_map.TryGetValue(project_storage, out files))
				{
					files = new List<string>();
					files_map[project_storage] = files;
				}

				// Now that we know which files belong to this project, iterate the project files
				for (int iFile = iProjectFilesStart; iFile < iNextProjecFilesStart; iFile++)
				{					
					string old_name;
					if (add_origin.TryGetValue(rgpszMkDocuments[iFile], out old_name))
					{
						copy_files[rgpszMkDocuments[iFile]] = old_name;
						add_origin.Remove(rgpszMkDocuments[iFile]);
					}
					else
					{
						files.Add(rgpszMkDocuments[iFile]);
					}

					// Refresh the solution explorer glyphs for all projects containing this file
					System.Collections.Generic.IList<VSITEMSELECTION> nodes = GetControlledProjectsContainingFile(rgpszMkDocuments[iFile]);
					selected_items.AddRange(nodes);

					QueueFileStatusUpdate(project_storage, rgpszMkDocuments[iFile]);
				}
			}

			foreach (var storage in copy_files_map.Keys)
			{
				var copy_files = copy_files_map[storage];
				foreach (var pair in copy_files)
				{
					var new_path = pair.Key;
					var old_path = pair.Value;

					Logger.WriteLine("Copying file: {0} from {1}",
						new_path, old_path);

					if (!storage.Copy(new_path, old_path))
					{
						Logger.WriteLine("Copy failed");

						List<string> files;
						if (!files_map.TryGetValue(storage, out files))
						{
							files = new List<string>();
							files_map[storage] = files;
						}

						files.Add(new_path);
					}
				}
			}

			foreach (var storage in files_map.Keys)
			{
				var files = files_map[storage];
				storage.AddFilesToStorage(files);
			}

			if (selected_items.Count != 0)
			{
//				_sccProvider.RefreshNodesGlyphs(selected_items);
				QueueSaveAllIfDirty();
			}

			if (add_origin.Count != 0)
			{
				foreach (var storage in copy_files_map.Keys)
				{
					var copy_files = copy_files_map[storage];

					foreach (var pair in copy_files)
					{
						var new_path = pair.Key;
						var old_path = pair.Value;

						Logger.WriteLine("Origin for file: {0} from {1}",
							new_path, old_path);
					}
				}
			}

			return VSConstants.S_OK;
		}

		public int OnQueryAddDirectories ([InAttribute] IVsProject pProject, [InAttribute] int cDirectories, [InAttribute] string[] rgpszMkDocuments, [InAttribute] VSQUERYADDDIRECTORYFLAGS[] rgFlags, [OutAttribute] VSQUERYADDDIRECTORYRESULTS[] pSummaryResult, [OutAttribute] VSQUERYADDDIRECTORYRESULTS[] rgResults)
		{
			return VSConstants.E_NOTIMPL;
		}

		public int OnAfterAddDirectoriesEx([InAttribute] int cProjects, [InAttribute] int cDirectories, [InAttribute] IVsProject[] rgpProjects, [InAttribute] int[] rgFirstIndices, [InAttribute] string[] rgpszMkDocuments, [InAttribute] VSADDDIRECTORYFLAGS[] rgFlags)
		{
			QueueSaveAllIfDirty();
			return VSConstants.S_OK;
		}

		/// <summary>
		/// Implement OnQueryRemoveFilesevent to warn the user when he's deleting controlled files.
		/// The user gets the chance to cancel the file removal.
		/// </summary>
		public int OnQueryRemoveFiles([InAttribute] IVsProject pProject, [InAttribute] int cFiles, [InAttribute] string[] rgpszMkDocuments, [InAttribute] VSQUERYREMOVEFILEFLAGS[] rgFlags, [OutAttribute] VSQUERYREMOVEFILERESULTS[] pSummaryResult, [OutAttribute] VSQUERYREMOVEFILERESULTS[] rgResults)
		{
			pSummaryResult[0] = VSQUERYREMOVEFILERESULTS.VSQUERYREMOVEFILERESULTS_RemoveOK;
			if (rgResults != null)
			{
				for (int iFile = 0; iFile < cFiles; iFile++)
				{
					Logger.WriteLine("OnQueryRemoveFiles: [{0}]: {1}", iFile, rgpszMkDocuments[iFile]);
					rgResults[iFile] = VSQUERYREMOVEFILERESULTS.VSQUERYREMOVEFILERESULTS_RemoveOK;
				}
			}

			try
			{
				var sccProject = pProject as IVsSccProject2;
				var pHier = pProject as IVsHierarchy;
				string projectName = null;
				if (sccProject == null)
				{
					// This is the solution calling
					pHier = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));
					projectName = _sccProvider.GetSolutionFileName();
				}
				else
				{
					// If the project doesn't support source control, it will be skipped
					if (sccProject != null)
					{
						projectName = _sccProvider.GetProjectFileName(sccProject);
					}
				}
				
				if (projectName != null)
				{
					for (int iFile = 0; iFile < cFiles; iFile++)
					{
						var storage = GetStorageForProject(pHier);
						if (storage != null)
						{
							SourceControlStatus status = storage.GetFileStatus(rgpszMkDocuments[iFile]);
							if (status != SourceControlStatus.scsUncontrolled)
							{
							}
						}
					}
				}
			}
			catch (Exception)
			{
				pSummaryResult[0] = VSQUERYREMOVEFILERESULTS.VSQUERYREMOVEFILERESULTS_RemoveNotOK;
				if (rgResults != null)
				{
					for (int iFile = 0; iFile < cFiles; iFile++)
					{
						rgResults[iFile] = VSQUERYREMOVEFILERESULTS.VSQUERYREMOVEFILERESULTS_RemoveNotOK;
					}
				}
			}
			
			return VSConstants.S_OK;
		}

		public int OnAfterRemoveFiles([InAttribute] int cProjects, [InAttribute] int cFiles, [InAttribute] IVsProject[] rgpProjects, [InAttribute] int[] rgFirstIndices, [InAttribute] string[] rgpszMkDocuments, [InAttribute] VSREMOVEFILEFLAGS[] rgFlags)
		{
			var files_map = new Dictionary<SccProviderStorage, List<string>>();
			var pending_files_map = new Dictionary<SccProviderStorage, List<string>>();

			// Start by iterating through all projects calling this function
			for (int iProject = 0; iProject < cProjects; iProject++)
			{
				var sccProject = rgpProjects[iProject] as IVsSccProject2;
				var pHier = rgpProjects[iProject] as IVsHierarchy;
				string projectName = null;

				if (sccProject == null)
				{
					// This is the solution calling
					pHier = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));
					projectName = _sccProvider.GetSolutionFileName();
				}
				else
				{
					if (sccProject == null)
					{
						// It is a project that doesn't support source control, in which case it should be ignored
						continue;
					}

					projectName = _sccProvider.GetProjectFileName(sccProject);
				}

				// Files in this project are in rgszMkOldNames, rgszMkNewNames arrays starting with iProjectFilesStart index and ending at iNextProjecFilesStart-1
				int iProjectFilesStart = rgFirstIndices[iProject];
				int iNextProjecFilesStart = cFiles;
				if (iProject < cProjects - 1)
				{
					iNextProjecFilesStart = rgFirstIndices[iProject + 1];
				}

				var project_storage = GetStorageForProject(pHier);
				if (project_storage == null)
					continue;

				List<string> files;
				if (!files_map.TryGetValue(project_storage, out files))
				{
					files = new List<string>();
					files_map[project_storage] = files;
				}

				List<string> pending_files;
				if (!pending_files_map.TryGetValue(project_storage, out pending_files))
				{
					pending_files = new List<string>();
					pending_files_map[project_storage] = pending_files;
				}

				// Now that we know which files belong to this project, iterate the project files
				for (int iFile = iProjectFilesStart; iFile < iNextProjecFilesStart; iFile++)
				{
					if (!File.Exists(rgpszMkDocuments[iFile]))
					{
						files.Add(rgpszMkDocuments[iFile]);
					}
					else
					{
						Logger.WriteLine("Queuing pending delete: {0}", rgpszMkDocuments[iFile]);
						pending_files.Add(rgpszMkDocuments[iFile]);
					}
				}
			}

			foreach (var storage in files_map.Keys)
			{
				var files = files_map[storage];
				QueuePendingRemove(storage, files);
			}

			foreach (var storage in pending_files_map.Keys)
			{
				var files = pending_files_map[storage];
				if (files.Count != 0)
					QueuePendingDelete(storage, files);
			}

			QueueSaveAllIfDirty();
			return VSConstants.S_OK;
		}

		public int OnQueryRemoveDirectories([InAttribute] IVsProject pProject, [InAttribute] int cDirectories, [InAttribute] string[] rgpszMkDocuments, [InAttribute] VSQUERYREMOVEDIRECTORYFLAGS[] rgFlags, [OutAttribute] VSQUERYREMOVEDIRECTORYRESULTS[] pSummaryResult, [OutAttribute] VSQUERYREMOVEDIRECTORYRESULTS[] rgResults)
		{
			return VSConstants.E_NOTIMPL;
		}

		public int OnAfterRemoveDirectories([InAttribute] int cProjects, [InAttribute] int cDirectories, [InAttribute] IVsProject[] rgpProjects, [InAttribute] int[] rgFirstIndices, [InAttribute] string[] rgpszMkDocuments, [InAttribute] VSREMOVEDIRECTORYFLAGS[] rgFlags)
		{
			QueueSaveAllIfDirty();
			return VSConstants.S_OK;
		}

		public int OnQueryRenameFiles([InAttribute] IVsProject pProject, [InAttribute] int cFiles, [InAttribute] string[] rgszMkOldNames, [InAttribute] string[] rgszMkNewNames, [InAttribute] VSQUERYRENAMEFILEFLAGS[] rgFlags, [OutAttribute] VSQUERYRENAMEFILERESULTS[] pSummaryResult, [OutAttribute] VSQUERYRENAMEFILERESULTS[] rgResults)
		{
			return VSConstants.E_NOTIMPL;
		}

		/// <summary>
		/// Implement OnAfterRenameFiles event to rename a file in the source control store when it gets renamed in the project
		/// Also, rename the store if the project itself is renamed
		/// </summary>
		public int OnAfterRenameFiles([InAttribute] int cProjects, [InAttribute] int cFiles, [InAttribute] IVsProject[] rgpProjects, [InAttribute] int[] rgFirstIndices, [InAttribute] string[] rgszMkOldNames, [InAttribute] string[] rgszMkNewNames, [InAttribute] VSRENAMEFILEFLAGS[] rgFlags)
		{
			// Start by iterating through all projects calling this function
			for (int iProject = 0; iProject < cProjects; iProject++)
			{
				var sccProject = rgpProjects[iProject] as IVsSccProject2;
				var pHier = rgpProjects[iProject] as IVsHierarchy;
				string projectName = null;

				if (sccProject == null)
				{
					// This is the solution calling
					pHier = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));
					projectName = _sccProvider.GetSolutionFileName();
				}
				else
				{
					if (sccProject == null)
					{
						// It is a project that doesn't support source control, in which case it should be ignored
						continue;
					}

					projectName = _sccProvider.GetProjectFileName(sccProject);
				}

				// Files in this project are in rgszMkOldNames, rgszMkNewNames arrays starting with iProjectFilesStart index and ending at iNextProjecFilesStart-1
				int iProjectFilesStart = rgFirstIndices[iProject];
				int iNextProjecFilesStart = cFiles;
				if (iProject < cProjects - 1)
				{
					iNextProjecFilesStart = rgFirstIndices[iProject+1];
				}

				// Now that we know which files belong to this project, iterate the project files
				for (int iFile = iProjectFilesStart; iFile < iNextProjecFilesStart; iFile++)
				{
					Logger.WriteLine("OnAfterRenameFiles: [{0}]: {1} -> {2}", iFile, rgszMkOldNames[iFile], rgszMkNewNames[iFile]);
					var storage = GetStorageForProject(pHier);
					if (storage != null)
					{
						storage.RenameFileInStorage(rgszMkOldNames[iFile], rgszMkNewNames[iFile]);
						if (outside_projects.Contains(rgszMkOldNames[iFile]))
						{
							outside_projects.Remove(rgszMkOldNames[iFile]);
							outside_projects.Add(rgszMkNewNames[iFile]);
						}

						// And refresh the solution explorer glyphs because we affected the source control status of this file
						// Note that by now, the project should already know about the new file name being part of its hierarchy
						System.Collections.Generic.IList<VSITEMSELECTION> nodes = GetControlledProjectsContainingFile(rgszMkNewNames[iFile]);
						_sccProvider.RefreshNodesGlyphs(nodes);
					}
				}
			}

			QueueSaveAllIfDirty();
			return VSConstants.S_OK;
		}

		public int OnQueryRenameDirectories([InAttribute] IVsProject pProject, [InAttribute] int cDirs, [InAttribute] string[] rgszMkOldNames, [InAttribute] string[] rgszMkNewNames, [InAttribute] VSQUERYRENAMEDIRECTORYFLAGS[] rgFlags, [OutAttribute] VSQUERYRENAMEDIRECTORYRESULTS[] pSummaryResult, [OutAttribute] VSQUERYRENAMEDIRECTORYRESULTS[] rgResults)
		{
			return VSConstants.E_NOTIMPL;
		}

		public int OnAfterRenameDirectories([InAttribute] int cProjects, [InAttribute] int cDirs, [InAttribute] IVsProject[] rgpProjects, [InAttribute] int[] rgFirstIndices, [InAttribute] string[] rgszMkOldNames, [InAttribute] string[] rgszMkNewNames, [InAttribute] VSRENAMEDIRECTORYFLAGS[] rgFlags)
		{
			return VSConstants.E_NOTIMPL;
/*
			// Before checking in files, make sure all in-memory edits have been commited to disk 
			// by forcing a save of the solution. Ideally, only the files to be checked in should be saved...
			var sol = (IVsSolution)_sccProvider.GetService(typeof(SVsSolution));
			if (sol.SaveSolutionElement((uint)__VSSLNSAVEOPTIONS.SLNSAVEOPT_SaveIfDirty, null, 0) != VSConstants.S_OK)
			{
				// If saving the files failed, don't continue with the checkin
				//				return;
			}
			return VSConstants.S_OK;
*/
		}

		public int OnAfterSccStatusChanged([InAttribute] int cProjects, [InAttribute] int cFiles, [InAttribute] IVsProject[] rgpProjects, [InAttribute] int[] rgFirstIndices, [InAttribute] string[] rgpszMkDocuments, [InAttribute] uint[] rgdwSccStatus)
		{
			return VSConstants.E_NOTIMPL;
		}

		#region Files and Project Management Functions

		/// <summary>
		/// Returns whether this source control provider is the active scc provider.
		/// </summary>
		public bool Active
		{
			get { return _active; }
		}

		/// <summary>
		/// Variable containing the solution location in source control if the solution being loaded is controlled
		/// </summary>
		public string LoadingControlledSolutionLocation
		{
			set { _loadingControlledSolutionLocation = value; }
		}

		//-----------------------------------------------------------------------------
		public bool IsProjectControlledOutside(IVsHierarchy pHier)
		{
			var solution_hier = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));
			
			if (pHier == null)
			{
				// this is solution, get the solution hierarchy
				pHier = solution_hier;
			}

			if (pHier == solution_hier)
				return outside_projects.Contains(_sccProvider.GetSolutionFileName());

			return outside_projects.Contains(_sccProvider.GetProjectFileName((IVsSccProject2)pHier));
		}


		/// <summary>
		/// Checks whether the specified project or solution (pHier==null) is under source control
		/// </summary>
		/// <returns>True if project is controlled.</returns>
		public bool IsProjectControlled(IVsHierarchy pHier)
		{
			if (pHier == null)
			{
				// this is solution, get the solution hierarchy
				pHier = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));
			}

			return project_to_storage_map.ContainsKey(pHier);
		}

		//-----------------------------------------------------------------------------
		public bool IsWebSiteProject(IVsHierarchy pHier)
		{
			return pHier != null && website_projects.Contains(pHier);
		}

		/// <summary>
		/// Checks whether the specified project or solution (pHier==null) is offline
		/// </summary>
		/// <returns>True if project is offline.</returns>
		public bool IsProjectOffline(IVsHierarchy pHier)
		{
			if (pHier == null)
			{
				// this is solution, get the solution hierarchy
				pHier = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));
			}

			return _offlineProjects.Contains(pHier);
		}

		/// <summary>
		/// Toggle the offline status of the specified project or solution
		/// </summary>
		/// <returns>True if project is offline.</returns>
		public void ToggleOfflineStatus(IVsHierarchy pHier)
		{
			if (pHier == null)
			{
				// this is solution, get the solution hierarchy
				pHier = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));
			}

			if (_offlineProjects.Contains(pHier))
			{
				_offlineProjects.Remove(pHier);
			}
			else
			{
				_offlineProjects.Add(pHier);
			}
		}

		/// <summary>
		/// Adds the specified projects and solution to source control
		/// </summary>
		public bool AddProjectsToSourceControl(HashSet<IVsHierarchy> hashUncontrolledProjects, bool addSolutionToSourceControl)
		{
			string solutionFile = _sccProvider.GetSolutionFileName();
			var solution_dir = Path.GetDirectoryName(solutionFile);

			// Also, if the solution was selected to be added to scc, write in the solution properties the controlled status
			if (addSolutionToSourceControl)
			{
				var solHier = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));
				var found_storage = GetStorageForFile(solution_dir);
				var storage = found_storage;
				if (storage == null)
					storage = new SccProviderStorage();

				if (!storage.IsValid)
				{
					// Checking if there is allready a repository
					var err = storage.Init(solution_dir, SccOpenProjectFlags.None);
					if (err != SccErrors.Ok)
					{
						using (var dlg = new WpfToWinFormsProxy<HgSccHelper.UI.CreateRepositoryWindow>())
						{
							var wnd = dlg.Wnd;
							wnd.SolutionLocation = solution_dir;

							dlg.ShowDialog();

							var result = wnd.DialogResult;
							if (result != true)
								return false;

							err = storage.Init(wnd.ResultLocation, SccOpenProjectFlags.CreateIfNew);
							if (err != SccErrors.Ok)
							{
								var msg = String.Format("Unable to create repository at folowing location:\n{0}", wnd.ResultLocation);
								System.Windows.Forms.MessageBox.Show(msg, "Error", MessageBoxButtons.OK, MessageBoxIcon.Error);
								return false;
							}
						}
					}
				}

				outside_projects.Remove(solutionFile);

				project_to_storage_map[solHier] = storage;
				if (found_storage == null)
				{
					storage.UpdateEvent += UpdateEvent_Handler;
					storage_list.Add(storage);
				}

				if (HgSccOptions.Instance.UseSccBindings)
				{
					_sccProvider.SolutionHaveSccBindings = true;
					_sccProvider.SolutionHasDirtyProps = true;
				}
			}

			// A real source control provider will ask the user for a location where the projects will be controlled
			// From the user input it should create up to 4 strings that will pass them to the projects to persist, 
			// so next time the project is open from disk, it will callback source control package, and the package
			// could use the 4 binding strings to identify the correct database location of the project files.
			foreach (IVsHierarchy pHier in hashUncontrolledProjects)
			{
				var sccProject2 = (IVsSccProject2)pHier;

				var project_path = _sccProvider.GetProjectFileName(sccProject2);
				var project_dir = Path.GetDirectoryName(project_path);

				// Add the newly controlled projects now to the list of controlled projects in this solution
				var found_storage = GetStorageForFile(project_path);
				var storage = found_storage;
				if (storage == null)
					storage = new SccProviderStorage();

				if (!storage.IsValid)
				{
					// Checking if there is allready a repository
					var err = storage.Init(project_dir, SccOpenProjectFlags.None);
					if (err != SccErrors.Ok)
					{
						using (var dlg = new WpfToWinFormsProxy<HgSccHelper.UI.CreateRepositoryWindow>())
						{
							var wnd = dlg.Wnd;
							wnd.SolutionLocation = solution_dir;
							wnd.ProjectLocation = project_dir;
							wnd.SelectProjectOnLoad = true;

							dlg.ShowDialog();

							var result = wnd.DialogResult;
							if (result != true)
								return false;

							err = storage.Init(wnd.ResultLocation, SccOpenProjectFlags.CreateIfNew);
							if (err != SccErrors.Ok)
							{
								var msg = String.Format("Unable to create repository at folowing location:\n{0}", wnd.ResultLocation);
								System.Windows.Forms.MessageBox.Show(msg, "Error", MessageBoxButtons.OK, MessageBoxIcon.Error);
								return false;
							}
						}
					}
				}

				if (HgSccOptions.Instance.UseSccBindings)
				{
					sccProject2.SetSccLocation(SccProjectName, SccAuxPath, SccLocalPath, _sccProvider.ProviderName);
					projects_with_scc_bindings.Add(pHier);
				}

				outside_projects.Remove(project_path);

				project_to_storage_map[pHier] = storage;

				if (Directory.Exists(project_path))
					website_projects.Add(pHier);

				if (found_storage == null)
				{
					storage.UpdateEvent += UpdateEvent_Handler;
					storage_list.Add(storage);
				}
			}

			// Now save all the modified files
			var sol = (IVsSolution)_sccProvider.GetService(typeof(SVsSolution));
			sol.SaveSolutionElement((uint)__VSSLNSAVEOPTIONS.SLNSAVEOPT_SaveIfDirty, null, 0);

			// Add now the solution and project files to the source control database

			if (addSolutionToSourceControl)
			{
				var storage = GetStorageForProject((IVsHierarchy)sol);
				if (storage != null)
				{
					storage.AddFilesToStorage(new[] { solutionFile });
				}
			}

			foreach (IVsHierarchy pHier in hashUncontrolledProjects)
			{
				if (IsWebSiteProject(pHier))
				{
					// Do not add files from web site projects
					// User will have to add them manualy
					continue;
				}

				var sccProject2 = (IVsSccProject2)pHier;
				var files = _sccProvider.GetProjectFiles(sccProject2);

				var storage = GetStorageForProject(pHier);
				if (storage != null)
				{
					storage.AddFilesToStorage(files);
				}
			}

			// For all the projects added to source control, refresh their source control glyphs
			var nodes = new List<VSITEMSELECTION>();
			foreach (IVsHierarchy pHier in hashUncontrolledProjects)
			{
				VSITEMSELECTION vsItem;
				vsItem.itemid = VSConstants.VSITEMID_ROOT;
				vsItem.pHier = pHier;
				nodes.Add(vsItem);
			}

			// Also, add the solution if necessary to the list of glyphs to refresh
			if (addSolutionToSourceControl)
			{
				VSITEMSELECTION vsItem;
				vsItem.itemid = VSConstants.VSITEMID_ROOT;
				vsItem.pHier = null;
				nodes.Add(vsItem);
			}

			_sccProvider.RefreshNodesGlyphs(nodes);
			return true;
		}

		//-----------------------------------------------------------------------------
		public void ManuallyAddFiles(IVsHierarchy pHier, IList<VSITEMSELECTION> list)
		{
			var storage = GetStorageForProject(pHier);
			if (storage == null)
				return;

			var files = new List<string>();
			var scc_project = pHier as IVsSccProject2;
			if (scc_project == null)
				return;

			foreach (var item in list)
			{
				if (item.itemid == VSConstants.VSITEMID_ROOT)
				{
					// Do not recurse into selected project node,
					// otherwise we can add unwanted files for web site projects
					continue;
				}

				IList<string> sccFiles = _sccProvider.GetProjectFiles(scc_project, item.itemid);
				foreach (string file in sccFiles)
				{
					files.Add(file);
				}
			}

			if (files.Count != 0)
			{
				var nodes = new List<VSITEMSELECTION>();
				storage.AddFilesToStorage(files);

				foreach (var file in files)
					nodes.AddRange(GetControlledProjectsContainingFile(file));

				_sccProvider.RefreshNodesGlyphs(nodes);
			}
		}

		// The following methods are not very efficient
		// A good source control provider should maintain maps to identify faster to which project does a file belong
		// and check only the status of the files in that project; or simply, query one common storage about the file status

		/// <summary>
		/// Returns the source control status of the specified file
		/// </summary>
		public SourceControlStatus GetFileStatus(string filename)
		{
			// FIXME: Handle folders

			var storage = GetStorageForFile(filename);
			if (storage == null)
				return SourceControlStatus.scsUncontrolled;

			return storage.GetFileStatus(filename);
		}

		public void GetStatusForFiles(string[] files, SourceControlStatus[] statuses)
		{
			for (int i = 0; i < files.Length; ++i)
				statuses[i] = GetFileStatus(files[i]);
		}

		//------------------------------------------------------------------
		public void ViewHistory(string file)
		{
			var storage = GetStorageForFile(file);
			if (storage != null)
			{
				SourceControlStatus status = storage.GetFileStatus(file);
				if (status != SourceControlStatus.scsUncontrolled)
				{
					using (var sln_prj_reloader = new SlnOrProjectReloader(_sccProvider, all_projects))
					using (var rdt_files_reloader = new RdtFilesReloader(_sccProvider, all_projects))
					{
						storage.ViewHistory(file);
					}
				}
			}
		}

		//------------------------------------------------------------------
		public void Annotate(string file)
		{
			var storage = GetStorageForFile(file);
			if (storage != null)
			{
				SourceControlStatus status = storage.GetFileStatus(file);
				if (status != SourceControlStatus.scsUncontrolled)
				{
					using (var sln_prj_reloader = new SlnOrProjectReloader(_sccProvider, all_projects))
					using (var rdt_files_reloader = new RdtFilesReloader(_sccProvider, all_projects))
					{
						storage.Annotate(file);
					}
				}
			}
		}

		//------------------------------------------------------------------
		private void CompareUsingVsDiff(string file)
		{
			var storage = GetStorageForFile(file);
			if (storage != null)
			{
				SourceControlStatus status = storage.GetFileStatus(file);
				if (status != SourceControlStatus.scsUncontrolled)
				{
					string temp = Util.GetTempFileNameForFile(file);
					try
					{
						if (!storage.CheckoutFile(file, "", temp))
						{
							// error
							return;
						}

						using (var stream = new FileStream(temp, FileMode.Open, FileAccess.ReadWrite,
							FileShare.Read, 4096, FileOptions.DeleteOnClose))
						{
							var diff_service = _sccProvider.GetService(typeof(SVsDifferenceService)) as IVsDifferenceService;
							if (diff_service == null)
								return;

							diff_service.OpenComparisonWindow(temp, file);
						}
					}
					catch (Exception ex)
					{
						Logger.WriteLine("Error, unable to compare file: {0}", ex.Message);
					}

					return;
				}
			}
		}

		//------------------------------------------------------------------
		private void CompareUsingHgDiff(string file)
		{
			var storage = GetStorageForFile(file);
			if (storage != null)
			{
				SourceControlStatus status = storage.GetFileStatus(file);
				if (status != SourceControlStatus.scsUncontrolled)
				{

					// Since we can not call WPF windows directly from the package
					// we need to reset a diff tool exception handler and
					// show WPF window through WinForms proxy

					var diff_handler = Util.DiffExceptionHandler;
					try
					{
						Util.DiffExceptionHandler = null;
						storage.Compare(file);
					}
					catch (HgDiffException)
					{
						using (var proxy = new WpfToWinFormsProxy<DiffOptionsWindow>())
						{
							var wnd = proxy.Wnd;
							proxy.ShowDialog();
						}
					}
					finally
					{
						// Restore diff exception handler
						Util.DiffExceptionHandler = diff_handler;
					}

					return;
				}
			}
		}

		//------------------------------------------------------------------
		public void Compare(string file)
		{
			if (DiffTools.Instance.UseVsDiffTool)
			{
				CompareUsingVsDiff(file);
				return;
			}

			CompareUsingHgDiff(file);
		}

		//------------------------------------------------------------------
		public void ViewChangeLog(IVsHierarchy hier)
		{
			var storage = GetStorageForProject(hier);
			if (storage == null)
				return;

			using (var sln_prj_reloader = new SlnOrProjectReloader(_sccProvider, all_projects))
			using (var rdt_files_reloader = new RdtFilesReloader(_sccProvider, all_projects))
			{
				storage.ViewChangeLog();
			}
		}

		//------------------------------------------------------------------
		public void Grep(IVsHierarchy hier)
		{
			var storage = GetStorageForProject(hier);
			if (storage == null)
				return;

			using (var sln_prj_reloader = new SlnOrProjectReloader(_sccProvider, all_projects))
			using (var rdt_files_reloader = new RdtFilesReloader(_sccProvider, all_projects))
			{
				storage.Grep();
			}
		}

		//------------------------------------------------------------------
		/// <summary>
		/// Returns a list of controlled projects containing the specified file
		/// </summary>
		public System.Collections.Generic.IList<VSITEMSELECTION> GetControlledProjectsContainingFile(string file)
		{
			// Accumulate all the controlled projects that contain this file
			System.Collections.Generic.IList<VSITEMSELECTION> nodes = new List<VSITEMSELECTION>();

			foreach (IVsHierarchy pHier in all_projects)
			{
				var storage = GetStorageForProject(pHier);
				if (storage == null)
					continue;

				var solHier = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));
				if (solHier == pHier)
				{
					// This is the solution
					if (file.ToLower().CompareTo(_sccProvider.GetSolutionFileName().ToLower()) == 0)
					{
						VSITEMSELECTION vsItem;
						vsItem.itemid = VSConstants.VSITEMID_ROOT;
						vsItem.pHier = null;
						nodes.Add(vsItem);
					}
				}
				else
				{
					var pProject = pHier as IVsProject2;
					// See if the file is member of this project
					// Caveat: the IsDocumentInProject function is expensive for certain project types, 
					// you may want to limit its usage by creating your own maps of file2project or folder2project
					int fFound;
					uint itemid;
					VSDOCUMENTPRIORITY[] prio = new VSDOCUMENTPRIORITY[1];
					if (pProject != null && pProject.IsDocumentInProject(file, out fFound, prio, out itemid) == VSConstants.S_OK && fFound != 0)
					{
						VSITEMSELECTION vsItem;
						vsItem.itemid = itemid;
						vsItem.pHier = pHier;
						nodes.Add(vsItem);
					}
				}
			}

			return nodes;
		}

		//------------------------------------------------------------------
		public System.Collections.Generic.IList<VSITEMSELECTION> GetControlledProjectsContainingFiles(IEnumerable<string> files)
		{
			var nodes = new List<VSITEMSELECTION>();
			foreach (var f in files)
			{
				var found = GetControlledProjectsContainingFile(f);
				nodes.AddRange(found);
			}

			return nodes;
		}

		//------------------------------------------------------------------
		public void CommitFiles(IVsHierarchy hier, IEnumerable<string> files)
		{
			var storage = GetStorageForProject(hier);
			if (storage == null)
				return;

			using (var sln_prj_reloader = new SlnOrProjectReloader(_sccProvider, all_projects))
			using (var rdt_files_reloader = new RdtFilesReloader(_sccProvider, all_projects))
			{
				IEnumerable<string> commited_files;
				storage.Commit(files, out commited_files);

				var list = GetControlledProjectsContainingFiles(commited_files);
				if (list.Count != 0)
				{
					// now refresh the selected nodes' glyphs
					_sccProvider.RefreshNodesGlyphs(list);
				}
			}
		}

		//------------------------------------------------------------------
		public void RevertFiles(IVsHierarchy hier, IEnumerable<string> files)
		{
			var storage = GetStorageForProject(hier);
			if (storage == null)
				return;

			using (var sln_prj_reloader = new SlnOrProjectReloader(_sccProvider, all_projects))
			using (var rdt_files_reloader = new RdtFilesReloader(_sccProvider, all_projects))
			{
				IEnumerable<string> reverted_files = null;
				storage.Revert(files, out reverted_files);

				var list = GetControlledProjectsContainingFiles(reverted_files);
				if (list.Count != 0)
				{
					// now refresh the selected nodes' glyphs
					_sccProvider.RefreshNodesGlyphs(list);
				}
			}
		}
		#endregion

		#region Implementation of IVsTrackProjectDocumentsEvents3

		/// <summary>
		/// Indicates that a project is about start a batch query process.
		/// </summary>
		/// <returns>
		/// If the method succeeds, it returns <see cref="F:Microsoft.VisualStudio.VSConstants.S_OK" />. If it fails, it returns an error code.
		/// </returns>
		public int OnBeginQueryBatch()
		{
			return VSConstants.S_OK;
		}

		/// <summary>
		/// Determines whether it is okay to proceed with the actual batch operation after successful completion of a batch query process. 
		/// </summary>
		/// <returns>
		/// If the method succeeds, it returns <see cref="F:Microsoft.VisualStudio.VSConstants.S_OK" />. If it fails, it returns an error code.
		/// </returns>
		/// <param name="pfActionOK">[out] Returns nonzero if it is okay to continue with the proposed batch process. Returns zero if the proposed batch process should not proceed.</param>
		public int OnEndQueryBatch(out int pfActionOK)
		{
			pfActionOK = 1;
			return VSConstants.S_OK;
		}

		/// <summary>
		/// This method is called to indicate that a batch query process has been canceled.
		/// </summary>
		/// <returns>
		/// If the method succeeds, it returns <see cref="F:Microsoft.VisualStudio.VSConstants.S_OK" />. If it fails, it returns an error code.
		/// </returns>
		public int OnCancelQueryBatch()
		{
			Logger.WriteLine("OnCancelQueryBatch");
			return VSConstants.S_OK;
		}

		/// <summary>
		/// Determines if it is okay to add a collection of files (possibly from source control) whose final destination may be different from a source location.
		/// </summary>
		/// <returns>
		/// If the method succeeds, it returns <see cref="F:Microsoft.VisualStudio.VSConstants.S_OK" />. If it fails, it returns an error code.
		/// </returns>
		/// <param name="pProject">[in] Project making the request about adding files.</param>
		/// <param name="cFiles">[in] The number of files represented in the <paramref name="rgpszNewMkDocuments" />, <paramref name="rgpszSrcMkDocuments" />, <paramref name="rgFlags" />, and <paramref name="rgResults" /> arrays.</param>
		/// <param name="rgpszNewMkDocuments">[in] An array of file names that indicate the files' final destination.</param>
		/// <param name="rgpszSrcMkDocuments">[in] An array of file names specifying the source location of the files.</param>
		/// <param name="rgFlags">[in] An array of values, one element for each file, from the <see cref="T:Microsoft.VisualStudio.Shell.Interop.VSQUERYADDFILEFLAGS" /> enumeration.</param>
		/// <param name="pSummaryResult">[out] Returns an overall status for all files as a value from the <see cref="T:Microsoft.VisualStudio.Shell.Interop.VSQUERYADDFILERESULTS" /> enumeration.</param>
		/// <param name="rgResults">[out] An array that is to be filled in with the status of each file. Each status is a value from the <see cref="T:Microsoft.VisualStudio.Shell.Interop.VSQUERYADDFILERESULTS" /> enumeration.</param>
		public int OnQueryAddFilesEx(IVsProject pProject, int cFiles, string[] rgpszNewMkDocuments, string[] rgpszSrcMkDocuments, VSQUERYADDFILEFLAGS[] rgFlags, VSQUERYADDFILERESULTS[] pSummaryResult, VSQUERYADDFILERESULTS[] rgResults)
		{
			pSummaryResult[0] = VSQUERYADDFILERESULTS.VSQUERYADDFILERESULTS_AddOK;
			if (rgResults != null)
			{
				for (int iFile = 0; iFile < cFiles; iFile++)
				{
					Logger.WriteLine("OnQueryAddFilesEx: [{0}]: {1} to {2}",
						iFile, rgpszSrcMkDocuments[iFile], rgpszNewMkDocuments[iFile]);
					rgResults[iFile] = VSQUERYADDFILERESULTS.VSQUERYADDFILERESULTS_AddOK;
				}
			}

			try
			{
				var sccProject = pProject as IVsSccProject2;
				var pHier = pProject as IVsHierarchy;
				string projectName = null;
				if (sccProject == null)
				{
					// This is the solution calling
					pHier = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));
					projectName = _sccProvider.GetSolutionFileName();
				}
				else
				{
					// If the project doesn't support source control, it will be skipped
					if (sccProject != null)
					{
						projectName = _sccProvider.GetProjectFileName(sccProject);
					}
				}

				if (projectName != null)
				{
					var storage = GetStorageForProject(pHier);

					for (int iFile = 0; iFile < cFiles; iFile++)
					{
						if (storage != null && rgpszSrcMkDocuments[iFile] != rgpszNewMkDocuments[iFile])
						{
							SourceControlStatus status = storage.GetFileStatus(rgpszSrcMkDocuments[iFile]);
							if (status != SourceControlStatus.scsUncontrolled)
							{
								if (storage.IsPathUnderRoot(rgpszNewMkDocuments[iFile]))
								{
									Logger.WriteLine("Add origin: {0} from {1}",
										rgpszNewMkDocuments[iFile], rgpszSrcMkDocuments[iFile]);

									var new_path = System.IO.Path.Combine(rgpszNewMkDocuments[iFile],
										System.IO.Path.GetFileName(rgpszSrcMkDocuments[iFile]));

									add_origin[new_path] = rgpszSrcMkDocuments[iFile];
								}
							}
						}
					}
				}
			}
			catch (Exception)
			{
				add_origin.Clear();

				pSummaryResult[0] = VSQUERYADDFILERESULTS.VSQUERYADDFILERESULTS_AddNotOK;
				if (rgResults != null)
				{
					for (int iFile = 0; iFile < cFiles; iFile++)
					{
						rgResults[iFile] = VSQUERYADDFILERESULTS.VSQUERYADDFILERESULTS_AddNotOK;
					}
				}
			}

			return VSConstants.S_OK;
		}

		/// <summary>
		/// Accesses a specified set of files and asks all implementers of this method to release any locks that may exist on those files.
		/// </summary>
		/// <returns>
		/// If the method succeeds, it returns <see cref="F:Microsoft.VisualStudio.VSConstants.S_OK" />. If it fails, it returns an error code.
		/// </returns>
		/// <param name="grfRequiredAccess">[in] A value from the <see cref="T:Microsoft.VisualStudio.Shell.Interop.__HANDSOFFMODE" /> enumeration, indicating the type of access requested. This can be used to optimize the locks that actually need to be released.</param>
		/// <param name="cFiles">[in] The number of files in the <paramref name="rgpszMkDocuments" /> array.</param>
		/// <param name="rgpszMkDocuments">[in] If there are any locks on this array of file names, the caller wants them to be released.</param>
		public int HandsOffFiles(uint grfRequiredAccess, int cFiles, string[] rgpszMkDocuments)
		{
			Logger.WriteLine("HandsOffFiles");
			foreach (var f in rgpszMkDocuments)
			{
				Logger.WriteLine("HOff: {0}", f);
			}
			return VSConstants.S_OK;
		}

		/// <summary>
		/// Called when a project has completed operations on a set of files.
		/// </summary>
		/// <returns>
		/// If the method succeeds, it returns <see cref="F:Microsoft.VisualStudio.VSConstants.S_OK" />. If it fails, it returns an error code.
		/// </returns>
		/// <param name="cFiles">[in] Number of file names given in the <paramref name="rgpszMkDocuments" /> array.</param>
		/// <param name="rgpszMkDocuments">[in] An array of file names.</param>
		public int HandsOnFiles(int cFiles, string[] rgpszMkDocuments)
		{
			Logger.WriteLine("HandsOnFiles");
			foreach (var f in rgpszMkDocuments)
			{
				Logger.WriteLine("HOn: {0}", f);
			}

			return VSConstants.S_OK;
		}

		#endregion

		//-----------------------------------------------------------------------------
		void QueueFileStatusUpdate(SccProviderStorage storage, string file)
		{
			lock (rdt_files_to_update)
			{
				HashSet<string> files_to_update;
				if (!rdt_files_to_update.TryGetValue(storage, out files_to_update))
				{
					files_to_update = new HashSet<string>();
					rdt_files_to_update[storage] = files_to_update;
				}

				files_to_update.Add(file);

				rdt_timer.Start();
			}
		}

		//------------------------------------------------------------------
		void Rdt_AfterSaveEvent(object sender, RdtAfterSaveEventArgs e)
		{
			Logger.WriteLine("OnAfterSave: {0}, flags {1}", e.DocInfo.MkDocument, e.DocInfo.Flags);

			var storage = GetStorageForFile(e.DocInfo.MkDocument);

			if (storage != null && storage.IsValid)
			{
				var status = storage.GetFileStatus(e.DocInfo.MkDocument);
				if (status != SourceControlStatus.scsUncontrolled)
					QueueFileStatusUpdate(storage, e.DocInfo.MkDocument);
			}
		}

		//------------------------------------------------------------------
		void rdt_timer_Tick(object sender, EventArgs e)
		{
			rdt_timer.Stop();
			QueuePendingCommand(CommandId.icmdPendingTask);
		}

		//------------------------------------------------------------------
		void Rdt_AfterAttributeChangeEvent(object sender, RdtAfterAttributeChangeEventArgs e)
		{
			Logger.WriteLine("OnAfterAttributeChange: {0}, {1}",
				e.DocInfo.MkDocument, e.Attributes);

			var storage = GetStorageForFile(e.DocInfo.MkDocument);

			if (storage != null && storage.IsValid)
			{
				var status = storage.GetFileStatus(e.DocInfo.MkDocument);
				if (status != SourceControlStatus.scsUncontrolled)
				{
					if ((e.Attributes & __VSRDTATTRIB.RDTA_DocDataIsDirty) != 0)
					{
						// If the file status is dirty, then there is no need to ask mercurial for file status,
						// because we will draw a pencil glyph anyway
						IList<VSITEMSELECTION> lst = GetControlledProjectsContainingFiles(new[] { e.DocInfo.MkDocument });
						if (lst.Count != 0)
							_sccProvider.RefreshNodesGlyphs(lst);
					}
					else
					{
						QueueFileStatusUpdate(storage, e.DocInfo.MkDocument);
					}
				}
			}
		}

		//-----------------------------------------------------------------------------
		public void RefreshGlyphsForControlledProjects()
		{
			// For all the projects added to source control, refresh their source control glyphs
			var nodes = new List<VSITEMSELECTION>();
			foreach (IVsHierarchy pHier in all_projects)
			{
				var storage = GetStorageForProject(pHier);
				if (storage != null)
				{
					VSITEMSELECTION vsItem;
					vsItem.itemid = VSConstants.VSITEMID_ROOT;
					vsItem.pHier = pHier;
					nodes.Add(vsItem);
				}
			}

			_sccProvider.RefreshNodesGlyphs(nodes);
		}

		//------------------------------------------------------------------
		public void Synchronize(IVsHierarchy hier)
		{
			var storage = GetStorageForProject(hier);
			if (storage == null)
				return;

			using (var sln_prj_reloader = new SlnOrProjectReloader(_sccProvider, all_projects))
			using (var rdt_files_reloader = new RdtFilesReloader(_sccProvider, all_projects))
			{
				storage.Synchronize();
			}
		}

		//-----------------------------------------------------------------------------
		private static bool TryGetLocalPath(string url, out string local_path)
		{
			try
			{
				var uri = new Uri(url);
				if (uri.IsFile)
				{
					local_path = uri.LocalPath;
					if (Directory.Exists(local_path))
						return true;
				}
			}
			catch (UriFormatException)
			{
			}

			local_path = "";
			return false;
		}

		//-----------------------------------------------------------------------------
		private static List<string> FindSolutions(string local_path)
		{
			var solutions = new List<string>();

			try
			{
				string[] files = Directory.GetFiles(local_path, "*.sln", SearchOption.AllDirectories);
				var solution_files =
					files.Where(
						f => f.EndsWith("sln", StringComparison.InvariantCultureIgnoreCase));

				solutions.AddRange(solution_files);
				solutions.Sort();

				return solutions;
			}
			catch (Exception)
			{
			}

			return solutions;
		}

		//------------------------------------------------------------------
		public void Clone(IVsHierarchy hier)
		{
			string source_path = null;

			var storage = GetStorageForProject(hier);
			if (storage != null && storage.IsValid)
			{
				source_path = storage.WorkingDir;
			}

			CloneResult clone_result;

			using (var proxy = new WpfToWinFormsProxy<CloneWindow>())
			{
				var wnd = proxy.Wnd;
				if (!String.IsNullOrEmpty(source_path))
					wnd.SourcePath = Path.GetFullPath(source_path);
	
				proxy.ShowDialog();

				if (wnd.CloneResult == null)
					return;

				clone_result = wnd.CloneResult;
			}

			// TODO: Add option to skip automatic opening of cloned reposotiry

			string local_path;
			if (!TryGetLocalPath(clone_result.Destination, out local_path))
				return;

			var solutions = FindSolutions(local_path);
			if (solutions.Count == 0)
				return;

			if (solutions.Count == 1 && _sccProvider.GetSolutionFileName() == null)
			{
				// There is only one solution in the cloned repository
				// and no loaded solution in the IDE
				
				// So, it is safe to automaticaly load a solution

				var solution_file = solutions[0];

				var sol = (IVsSolution)_sccProvider.GetService(typeof(SVsSolution));
				int error = sol.OpenSolutionFile((uint)__VSSLNOPENOPTIONS.SLNOPENOPT_Silent, solution_file);
				if (error != VSConstants.S_OK)
				{
					Logger.WriteLine("Error: {0}", error);

					var msg = String.Format("Unable to load solution:\n{0}", solution_file);
					MessageBox.Show(msg, "Error", MessageBoxButtons.OK,
					                MessageBoxIcon.Error);
				}
				return;
			}

			// There are multiple solutions and/or allready loaded solution in the IDE,
			// so ask user to select a solution to load or to cancel

			using (var proxy = new WpfToWinFormsProxy<SelectSolutionWindow>())
			{
				var wnd = proxy.Wnd;
				wnd.Solutions = solutions;

				proxy.ShowDialog();

				if (wnd.DialogResult == true && !String.IsNullOrEmpty(wnd.SelectedSolution))
				{
					var solution_file = wnd.SelectedSolution;

					var sol = (IVsSolution)_sccProvider.GetService(typeof(SVsSolution));
					int error = sol.OpenSolutionFile((uint)__VSSLNOPENOPTIONS.SLNOPENOPT_Silent, solution_file);

					if (error != VSConstants.S_OK)
					{
						Logger.WriteLine("Error: {0}", error);

						var msg = String.Format("Unable to load solution:\n{0}", solution_file);
						MessageBox.Show(msg, "Error", MessageBoxButtons.OK,
										MessageBoxIcon.Error);
					}
					return;
				}
			}
		}

		//------------------------------------------------------------------
		public void Options()
		{
			using (var proxy = new WpfToWinFormsProxy<OptionsWindow>())
			{
				var wnd = proxy.Wnd;
				wnd.Title = "HgSccPackage options";
				wnd.AddPage(new OptionsPageMain());
				wnd.AddPage(new OptionsPageTheme());
				wnd.AddPage(new OptionsPageDiffTools());
				wnd.AddPage(new HgSccHelper.BitBucket.OptionsPageBitBucket());
				wnd.AddPage(new HgSccHelper.Kiln.OptionsPageKiln());
				wnd.AddPage(new OptionsPageHttpProxy());
				wnd.AddPage(new OptionsPageAbout());
				proxy.ShowDialog();
			}
		}

		//------------------------------------------------------------------
		public void Update(IVsHierarchy hier)
		{
			var storage = GetStorageForProject(hier);
			if (storage == null)
				return;
				
			using (var sln_prj_reloader = new SlnOrProjectReloader(_sccProvider, all_projects))
			using (var rdt_files_reloader = new RdtFilesReloader(_sccProvider, all_projects))
			{
				storage.Update();
			}
		}

		//------------------------------------------------------------------
		public void Tags(IVsHierarchy hier)
		{
			var storage = GetStorageForProject(hier);
			if (storage != null)
				storage.Tags();
		}

		//------------------------------------------------------------------
		public void RefreshStatus()
		{
			foreach (var storage in storage_list)
				storage.ReloadCache();

			RefreshGlyphsForControlledProjects();

/*
			var solution = _sccProvider.GetService<IVsSolution>();
			foreach (var item in solution.TraverseItems())
			{
				var ident_str = new string(' ', item.Depth * 2);
				Logger.WriteLine("{0}{1}({2})", ident_str, item.HierarchyNode.Name, item.HierarchyNode.Id);
			}
*/
		}

		//------------------------------------------------------------------
		private void UpdateEvent_Handler(object sender, EventArgs e)
		{
			var storage = sender as SccProviderStorage;
			if (storage != null)
			{
				storage.ReloadCache();
				RefreshGlyphsForControlledProjects();
			}
		}

		//------------------------------------------------------------------
		public bool IsValidStorage(IVsHierarchy hier)
		{
			var storage = GetStorageForProject(hier);
			return storage != null && storage.IsValid;
		}

		//------------------------------------------------------------------
		public bool IsAnyModifedFiles(IVsHierarchy hier)
		{
			var storage = GetStorageForProject(hier);
			return storage != null && storage.IsAnyModifiedFiles();
		}

		#region IVsSccGlyphs Members

		public int GetCustomGlyphList(uint BaseIndex, out IntPtr pdwImageListHandle)
		{
			Logger.WriteLine("GetCustomGlyphList");

			// If this is the first time we got called, construct the image list, remember the index, etc
			if (this.customSccGlyphsImageList == null)
			{
				// The shell calls this function when the provider becomes active to get our custom glyphs
				// and to tell us what's the first index we can use for our glyphs
				// Remember the index in the scc glyphs (VsStateIcon) where our custom glyphs will start
				this.customSccGlyphBaseIndex = BaseIndex;

				// Create a new imagelist
				this.customSccGlyphsImageList = new ImageList();

				// Set the transparent color for the imagelist (the SccGlyphs.bmp uses magenta for background)
				this.customSccGlyphsImageList.TransparentColor = Color.FromArgb(255, 0, 255);

				// Set the corret imagelist size (7x16 pixels, otherwise the system will either stretch the image or fill in with black blocks)
				this.customSccGlyphsImageList.ImageSize = new Size(7, 16);

				// Add the custom scc glyphs we support to the list
				// NOTE: VS2005 and VS2008 are limited to 4 custom scc glyphs (let's hope this will change in future versions)
				Image sccGlyphs = (Image)Resources.CustomGlyphs;
				this.customSccGlyphsImageList.Images.AddStrip(sccGlyphs);
			}

			// Return a Win32 HIMAGELIST handle to our imagelist to the shell (by keeping the ImageList a member of the class we guarantee the Win32 object is still valid when the shell needs it)
			pdwImageListHandle = this.customSccGlyphsImageList.Handle;

			// Return success (If you don't want to have custom glyphs return VSConstants.E_NOTIMPL)
			return VSConstants.S_OK;
		}

		#endregion

		//-----------------------------------------------------------------------------
		bool SccBindProject(IVsHierarchy hier)
		{
			if (!IsSccBoundProject(hier))
			{
				IVsSccProject2 prj = hier as IVsSccProject2;
				if (prj != null)
				{
					prj.SetSccLocation(SccProjectName, SccAuxPath, SccLocalPath, _sccProvider.ProviderName);

					var sol = (IVsSolution)_sccProvider.GetService(typeof(SVsSolution));
					sol.SaveSolutionElement((uint)__VSSLNSAVEOPTIONS.SLNSAVEOPT_SaveIfDirty, hier, 0);
					sol.SaveSolutionElement((uint)__VSSLNSAVEOPTIONS.SLNSAVEOPT_SaveIfDirty, (IVsHierarchy)sol, 0);

					projects_with_scc_bindings.Add(hier);
					return true;
				}
			}

			return false;
		}

		//-----------------------------------------------------------------------------
		bool SccUnbindProject(IVsHierarchy hier)
		{
			if (IsSccBoundProject(hier))
			{
				IVsSccProject2 prj = hier as IVsSccProject2;
				if (prj != null)
				{
					prj.SetSccLocation("", "", "", "");

					var sol = (IVsSolution)_sccProvider.GetService(typeof(SVsSolution));
					sol.SaveSolutionElement((uint)__VSSLNSAVEOPTIONS.SLNSAVEOPT_SaveIfDirty, hier, 0);
					sol.SaveSolutionElement((uint)__VSSLNSAVEOPTIONS.SLNSAVEOPT_SaveIfDirty, (IVsHierarchy)sol, 0);

					projects_with_scc_bindings.Remove(hier);
					return true;
				}
			}

			return false;
		}

		//-----------------------------------------------------------------------------
		bool IsSccBoundProject(IVsHierarchy hier)
		{
			return projects_with_scc_bindings.Contains(hier);
		}

		//-----------------------------------------------------------------------------
		bool SccBindSolution(IVsHierarchy hier)
		{
			if (!_sccProvider.SolutionHaveSccBindings)
			{
				_sccProvider.SolutionHaveSccBindings = true;
				_sccProvider.SolutionHasDirtyProps = true;

				var sol = (IVsSolution)_sccProvider.GetService(typeof(SVsSolution));
				sol.SaveSolutionElement((uint)__VSSLNSAVEOPTIONS.SLNSAVEOPT_SaveIfDirty, hier, 0);

				return true;
			}

			return false;
		}

		//-----------------------------------------------------------------------------
		bool SccUnbindSolution(IVsHierarchy hier)
		{
			if (_sccProvider.SolutionHaveSccBindings)
			{
				_sccProvider.SolutionHaveSccBindings = false;
				_sccProvider.SolutionHasDirtyProps = true;

				var sol = (IVsSolution)_sccProvider.GetService(typeof(SVsSolution));
				sol.SaveSolutionElement((uint)__VSSLNSAVEOPTIONS.SLNSAVEOPT_SaveIfDirty, hier, 0);

				return true;
			}

			return false;
		}

		//------------------------------------------------------------------
		string GetHierarchyName(IVsHierarchy hier)
		{
			object name;
			if (VSConstants.S_OK == hier.GetProperty((uint)VSConstants.VSITEMID_ROOT, (int)__VSHPROPID.VSHPROPID_Name, out name))
			{
				var str_name = name as string;
				if (str_name != null)
					return str_name;
			}

			return "";
		}

		//------------------------------------------------------------------
		internal void ChangeSccBindings()
		{
			using (var proxy = new WpfToWinFormsProxy<ChangeSccBindingsWindow>())
			{
				var wnd = proxy.Wnd;
				var projects = new List<SccBindItem>();
				var sln_hier = (IVsHierarchy)_sccProvider.GetService(typeof(SVsSolution));

				foreach(var hier in project_to_storage_map.Keys)
				{
					var item = new SccBindItem();
					item.Hierarchy = hier;

					var project = hier as IVsProject;
					if (project != null)
					{
						var project_path = _sccProvider.GetProjectFileName(project);
						if (project_path != null && !outside_projects.Contains(project_path))
						{
							item.Path = project_path;
							item.Name = GetHierarchyName(hier);
							item.SccProjectType = SccProjectType.Project;
							item.SccBindStatus = SccBindStatus.NotBound;
							if (IsSccBoundProject(hier))
								item.SccBindStatus = SccBindStatus.Bound;
							item.Bind = SccBindProject;
							item.Unbind = SccUnbindProject;

							projects.Add(item);
						}
					}
					else
					{
						var scc_solution = hier as IVsSolution;
						var solution_path = _sccProvider.GetSolutionFileName();
						if (scc_solution != null && !outside_projects.Contains(solution_path))
						{
							item.Path = solution_path;
							item.Name = GetHierarchyName(hier);
							item.SccProjectType = SccProjectType.Solution;
							item.SccBindStatus = SccBindStatus.NotBound;
							if (_sccProvider.SolutionHaveSccBindings)
								item.SccBindStatus = SccBindStatus.Bound;

							item.Bind = SccBindSolution;
							item.Unbind = SccUnbindSolution;
							projects.Add(item);
						}
					}					
				}

				wnd.SccBindItems = projects;
				proxy.ShowDialog();
			}
		}
	}

	//------------------------------------------------------------------
	class UpdateStatusParams
	{
		public SccProviderStorage Storage { get; set; }
		public IEnumerable<string> Files { get; set; }
	}

	//------------------------------------------------------------------
	class UpdateStatusResults
	{
		public SccProviderStorage Storage { get; set; }
		public List<HgFileInfo> FilesInfo { get; set; }
	}
}