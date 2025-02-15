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
using System.Linq;
using System.Text;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Data;
using System.Windows.Documents;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Imaging;
using System.Windows.Shapes;
using System.Windows.Threading;
using System.Collections.ObjectModel;
using HgSccHelper.CommandServer;
using Microsoft.Win32;

namespace HgSccHelper
{
	//==================================================================
	public partial class ArchiveWindow : Window
	{
		//-----------------------------------------------------------------------------
		public string WorkingDir { get; set; }

		//------------------------------------------------------------------
		public string ArchiveRevision { get; set; }

		//------------------------------------------------------------------
		public UpdateContextCache UpdateContextCache { get; set; }

		//------------------------------------------------------------------
		HgClient HgClient { get { return UpdateContextCache.HgClient; } }

		DispatcherTimer timer;
		RevLogChangeDesc Target { get; set; }

		ObservableCollection<ArchiveTypeInfo> archive_types;

		//-----------------------------------------------------------------------------
		private string DestinationPath
		{
			get { return (string)this.GetValue(DestinationPathProperty); }
			set { this.SetValue(DestinationPathProperty, value); }
		}

		//-----------------------------------------------------------------------------
		public static readonly DependencyProperty DestinationPathProperty =
			DependencyProperty.Register("DestinationPath", typeof(string),
			typeof(ArchiveWindow));

		//-----------------------------------------------------------------------------
		string ArchiveDirPart { get; set; }

		//-----------------------------------------------------------------------------
		string ArchiveRevisionPart { get; set; }

		public const string CfgPath = @"GUI\ArchiveWindow";
		CfgWindowPosition wnd_cfg;

		//------------------------------------------------------------------
		public ArchiveWindow()
		{
			wnd_cfg = new CfgWindowPosition(CfgPath, this, CfgWindowPositionOptions.PositionOnly);

			InitializeComponent();

			HgSccHelper.UI.ThemeManager.Instance.Subscribe(this);

			UpdateContextCache = new UpdateContextCache();

			// Since WPF combo box does not provide TextChanged event
			// register it from edit text box through combo box template

			comboRevision.Loaded += delegate
			{
				TextBox editTextBox = comboRevision.Template.FindName("PART_EditableTextBox", comboRevision) as TextBox;
				if (editTextBox != null)
				{
					editTextBox.TextChanged += OnComboTextChanged;
				}
			};

			comboRevision.Unloaded += delegate
			{
				TextBox editTextBox = comboRevision.Template.FindName("PART_EditableTextBox", comboRevision) as TextBox;
				if (editTextBox != null)
				{
					editTextBox.TextChanged -= OnComboTextChanged;
				}
			};

			archive_types = new ObservableCollection<ArchiveTypeInfo>();

			foreach (HgArchiveTypes archive_type in Enum.GetValues(typeof(HgArchiveTypes)))
			{
				archive_types.Add(new ArchiveTypeInfo
				{
					ArchiveType = archive_type,
					Extension = archive_type.FileExtension(),
					Description = archive_type.Description()
				});
			}

			comboArchiveType.ItemsSource = archive_types;
		}

		//------------------------------------------------------------------
		private void Window_Loaded(object sender, RoutedEventArgs e)
		{
			Title = string.Format("Arhive: '{0}'", WorkingDir);

			string archive_type;
			if (Cfg.Get(CfgPath, "ArchiveType", out archive_type, ""))
			{
				try
				{
					var type =
						(HgArchiveTypes) Enum.Parse(typeof (HgArchiveTypes), archive_type);

					var found_type = archive_types.FirstOrDefault(t => t.ArchiveType == type);
					if (found_type != null)
						comboArchiveType.SelectedItem = found_type;
				}
				catch (ArgumentException)
				{
				}
				catch (OverflowException)
				{
				}
			}

			ArchiveDirPart = WorkingDir;
			ArchiveRevisionPart = ArchiveRevision;

			timer = new DispatcherTimer();
			timer.Interval = TimeSpan.FromMilliseconds(200);
			timer.Tick += OnTimerTick;

			if (!string.IsNullOrEmpty(ArchiveRevision))
			{
				var target_desc = UpdateContextCache.TargetRevision;
				if (target_desc == null)
					target_desc = HgClient.GetRevisionDesc(ArchiveRevision);

				if (target_desc == null)
				{
					// error
					Close();
					return;
				}

				var item = new ArchiveComboItem();
				item.GroupText = "Rev";
				item.Rev = target_desc.Rev;
				item.Name = target_desc.Rev.ToString();
				item.SHA1 = target_desc.SHA1;
				item.Misc = "Target";

				comboRevision.Items.Add(item);
			}

			var bookmarks = UpdateContextCache.Bookmarks;
			if (bookmarks == null)
				bookmarks = HgClient.Bookmarks();

			foreach (var bookmark in bookmarks)
			{
				var item = new ArchiveComboItem();
				item.GroupText = "Bookmark";
				item.Name = bookmark.Name;
				item.Rev = bookmark.Rev;
				item.SHA1 = bookmark.SHA1;
				item.Misc = bookmark.IsCurrent ? "Current" : "";

				comboRevision.Items.Add(item);
			}

			var tags = UpdateContextCache.Tags;
			if (tags == null)
				tags = HgClient.Tags();

			foreach (var tag in tags)
			{
				var item = new ArchiveComboItem();
				item.GroupText = "Tag";
				item.Name = tag.Name;
				item.Rev = tag.Rev;
				item.SHA1 = tag.SHA1;
				item.Misc = tag.IsLocal ? "Local" : "";

				comboRevision.Items.Add(item);
			}

			var branches = UpdateContextCache.Branches;
			if (branches == null)
				branches = HgClient.Branches(HgBranchesOptions.Closed);

			foreach (var branch in branches)
			{
				var item = new ArchiveComboItem();
				item.GroupText = "Branch";
				item.Name = branch.Name;
				item.Rev = branch.Rev;
				item.SHA1 = branch.SHA1;
				item.Misc = "";
				if (!branch.IsActive)
					item.Misc = "Not Active";
				else
					if (branch.IsClosed)
						item.Misc = "Closed";

				comboRevision.Items.Add(item);
			}

			comboRevision.SelectedIndex = 0;
			comboRevision.Focus();

			if (comboArchiveType.SelectedIndex == -1)
				comboArchiveType.SelectedIndex = 0;

			RefreshTarget();
		}

		//------------------------------------------------------------------
		private void RefreshTarget()
		{
			var revision = comboRevision.Text;
			if (comboRevision.SelectedItem != null)
			{
				var item = (ArchiveComboItem)comboRevision.SelectedItem;
				revision = item.SHA1;
			}

			Target = null;
			if (!String.IsNullOrEmpty(revision))
				Target = HgClient.GetRevisionDesc(revision);

			if (Target == null)
			{
				revisionDesc.Text = "Invalid Revision";
				btnArchive.IsEnabled = false;
			}
			else
			{
				revisionDesc.Text = Target.GetDescription();
				btnArchive.IsEnabled = true;
				ArchiveRevisionPart = comboRevision.Text;
			}

			UpdateDestinationPath();
		}

		//------------------------------------------------------------------
		private void OnTimerTick(object o, EventArgs e)
		{
			timer.Stop();
			RefreshTarget();
		}

		//------------------------------------------------------------------
		private void Window_Closed(object sender, EventArgs e)
		{
			timer.Stop();
			timer.Tick -= OnTimerTick;

			var archive_type = comboArchiveType.SelectedItem as ArchiveTypeInfo;
			if (archive_type != null)
				Cfg.Set(CfgPath, "ArchiveType", archive_type.ArchiveType.ToString());
		}

		//------------------------------------------------------------------
		private void btnArchive_Click(object sender, RoutedEventArgs e)
		{
			if (Target == null)
			{
				MessageBox.Show("Invalid revision", "Error", MessageBoxButton.OK, MessageBoxImage.Error);
				return;
			}

			var options = HgArchiveOptions.None;
			if (checkNoFilesDecode.IsChecked == true)
				options = HgArchiveOptions.NoDecode;

			var hg_archive = new HgArchive();
			var archive_type = (ArchiveTypeInfo)comboArchiveType.SelectedItem;

			if (!hg_archive.Archive(WorkingDir, Target.SHA1, options, archive_type.ArchiveType, DestinationPath.Quote()))
			{
			    MessageBox.Show("An error occured while archive", "Error", MessageBoxButton.OK, MessageBoxImage.Error);
			    return;
			}

			MessageBox.Show("Archive was successfull", "Information", MessageBoxButton.OK, MessageBoxImage.Information);
			Close();
		}

		//------------------------------------------------------------------
		private void Cancel_Click(object sender, RoutedEventArgs e)
		{
			Close();
		}

		//------------------------------------------------------------------
		private void OnComboTextChanged(object sender, TextChangedEventArgs e)
		{
			timer.Start();
			btnArchive.IsEnabled = false;
		}

		//------------------------------------------------------------------
		private void Window_PreviewKeyDown(object sender, KeyEventArgs e)
		{
			if (e.Key == Key.Escape)
				Close();
		}

		//-----------------------------------------------------------------------------
		private void UpdateDestinationPath()
		{
			var archive_type = (ArchiveTypeInfo)comboArchiveType.SelectedItem;

			DestinationPath = String.Format("{0}_{1}{2}", ArchiveDirPart, ArchiveRevisionPart,
				archive_type.Extension);

			textDestPath.SelectAll();
		}

		//-----------------------------------------------------------------------------
		private void comboArchiveType_SelectionChanged(object sender, SelectionChangedEventArgs e)
		{
			UpdateDestinationPath();
		}

		//-----------------------------------------------------------------------------
		private void Button_Click(object sender, RoutedEventArgs e)
		{
			var info = (ArchiveTypeInfo)comboArchiveType.SelectedItem;

			if (info.ArchiveType == HgArchiveTypes.Files)
			{
				using (var dlg = new System.Windows.Forms.FolderBrowserDialog())
				{
					dlg.Description = "Browse for Destination Path...";
					dlg.ShowNewFolderButton = true;
					dlg.SelectedPath = WorkingDir;

					var result = dlg.ShowDialog();
					if (result == System.Windows.Forms.DialogResult.OK)
					{
						DestinationPath = dlg.SelectedPath;
						ArchiveDirPart = DestinationPath;
						textDestPath.SelectAll();
					}
				}
			}
			else
			{
				var dlg = new SaveFileDialog();
				dlg.AddExtension = true;
				dlg.CheckPathExists = false;
				dlg.CheckFileExists = false;
				dlg.FileName = DestinationPath;
				dlg.Filter = String.Format("{0}|*{1}", info.ArchiveType.Description(), info.ArchiveType.FileExtension());
				dlg.Title = "Browse for Destination Path...";
				dlg.RestoreDirectory = true;

				var result = dlg.ShowDialog(this);
				if (result == true)
				{
					DestinationPath = dlg.FileName;
					ArchiveDirPart = System.IO.Path.GetDirectoryName(DestinationPath);
					textDestPath.SelectAll();
				}
			}
		}
	}

	//------------------------------------------------------------------
	class ArchiveComboItem
	{
		public string GroupText { get; set; }
		public string Name { get; set; }
		public int Rev { get; set; }
		public string SHA1 { get; set; }
		public string Misc { get; set; }
	}

	//-----------------------------------------------------------------------------
	class ArchiveTypeInfo
	{
		public HgArchiveTypes ArchiveType { get; set; }
		public string Description { get; set; }
		public string Extension { get; set; }
	}
}
