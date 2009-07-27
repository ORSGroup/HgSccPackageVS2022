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

using System.Collections.Generic;

//==================================================================
namespace HgSccHelper
{
	public class LogLine
	{
		public string[] Parents {get; set;}
	}

	//------------------------------------------------------------------
	public struct LinePos
	{
		public int X1 { get; set; }
		public int X2 { get; set; }
	}

	//------------------------------------------------------------------
	public class RevLogLines
	{
		public RevLogChangeDesc ChangeDesc { get; set; }
		public int Pos { get; set; }
		public int Count { get; set; }
		public List<LinePos> Lines { get; set; }
	}

	//------------------------------------------------------------------
	public class RevLogLinesPair
	{
		public RevLogLines Prev { get; set; }
		public RevLogLines Current { get; set; }
		
		//------------------------------------------------------------------
		public static IEnumerable<RevLogLinesPair> FromV1(IEnumerable<RevLogLines> lines)
		{
			RevLogLines prev = null;
			foreach (var l in lines)
			{
				yield return new RevLogLinesPair { Prev = prev, Current = l };
				prev = l;
			}
		}
	}


	//==================================================================
	class RevLogIterator
	{
		//------------------------------------------------------------------
		public static IEnumerable<RevLogLines> GetLines(List<RevLogChangeDesc> revs)
		{
			var revisions = new List<string>();

			foreach (var rev in revs)
			{
				if (!revisions.Contains(rev.SHA1))
				{
					// new head
					revisions.Add(rev.SHA1);
				}

				int rev_index = revisions.IndexOf(rev.SHA1);
				var next_revs = new List<string>(revisions);
				var parents = rev.Parents;
				var parents_to_add = new List<string>();

				foreach (var parent in parents)
				{
					if (!next_revs.Contains(parent))
						parents_to_add.Add(parent);
				}

				next_revs.RemoveAt(rev_index);
				next_revs.InsertRange(rev_index, parents_to_add);

				var l = new RevLogLines();
				l.ChangeDesc = rev;
				l.Lines = new List<LinePos>();
				l.Pos = rev_index;
				l.Count = revisions.Count;

				for (int i = 0; i < revisions.Count; ++i)
				{
					int next_pos = next_revs.IndexOf(revisions[i]);
					if (next_pos != -1)
					{
						l.Lines.Add(new LinePos { X1 = i, X2 = next_pos });
					}
					else
					{
						if (revisions[i] == rev.SHA1)
						{
							foreach (var parent in parents)
							{
								int idx = next_revs.IndexOf(parent);
								l.Lines.Add(new LinePos { X1 = i, X2 = idx });
							}
						}
					}

				}

				yield return l;

				revisions = next_revs;
			}
		}
	}
}
