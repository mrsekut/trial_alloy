//
// Alloy Tutorial
// - File System
// - https://alloytools.org/tutorials/online/frame-FS-1.html
// - https://scrapbox.io/mrsekut-p/Tutorial_for_Alloy_Analyzer_4.0を読む
//

abstract sig FSObject { parent: lone Dir }

sig Dir extends FSObject { contents: set FSObject }
sig File extends FSObject { }

one sig Root extends Dir { } { no parent }


fact { all d: Dir, o: d.contents | o.parent = d }
fact { FSObject in Root.*contents }


// 上記の仕様に対し、循環してないことを確認
assert acyclic { no d: Dir | d in d.^contents }
check acyclic for 5

// 親は1つ
assert oneRoot { one d: Dir | no d.parent }
check oneRoot for 5

// 全てのファイルは、最大1つのディレクトリに属する
assert oneLocation { all o: FSObject | lone d: Dir | o in d.contents }
check oneLocation for 5

pred show {}

run show for 6

assert Wrong {
	all obj, p: (FSObject - Root) | (obj.parent = p.parent)
}
check Wrong for 11