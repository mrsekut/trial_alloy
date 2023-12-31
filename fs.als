//
// Alloy Tutorial
// - File System
// - https://alloytools.org/tutorials/online/frame-FS-1.html
// - https://scrapbox.io/mrsekut-p/Tutorial_for_Alloy_Analyzer_4.0を読む
//

// File system objects
abstract sig FSObject { }
sig File, Dir extends FSObject { }

// A File System
sig FileSystem {
  live: set FSObject,
  root: Dir & live,
  parent: (live - root) ->one (Dir & live),
  contents: Dir -> FSObject
}{
  // live objects are reachable from the root
  live in root.*contents
  // parent is the inverse of contents
  parent = ~contents
}

// Move x to directory d
pred move [fs, fs2: FileSystem, x: FSObject, d: Dir] {
  (x + d) in fs.live
  fs2.parent = fs.parent - x->(x.(fs.parent)) + x->d
}

// Delete the file or directory x
pred remove [fs, fs2: FileSystem, x: FSObject] {
  x in (fs.live - fs.root)
  fs2.root = fs.root
  fs2.parent = fs.parent - x->(x.(fs.parent))
}

// Recursively delete the object x
pred removeAll [fs, fs2: FileSystem, x: FSObject] {
  x in (fs.live - fs.root)
  fs2.root = fs.root
  let subtree = x.*(fs.contents) |
      fs2.parent = fs.parent - subtree->(subtree.(fs.parent))

}

run move for 2 FileSystem, 4 FSObject
run remove for 2 FileSystem, 4 FSObject
run removeAll for 2 FileSystem, 4 FSObject

// Moving doesn't add or delete any file system objects
moveOkay: check {
  all fs, fs2: FileSystem, x: FSObject, d:Dir |
    move[fs, fs2, x, d] => fs2.live = fs.live
} for 5

// remove removes exactly the specified file or directory
removeOkay: check {
  all fs, fs2: FileSystem, x: FSObject |
    remove[fs, fs2, x] => fs2.live = fs.live - x
} for 5

// removeAll removes exactly the specified subtree
removeAllOkay: check {
  all fs, fs2: FileSystem, d: Dir |
    removeAll[fs, fs2, d] => fs2.live = fs.live - d.*(fs.contents)
} for 5

// remove and removeAll has the same effects on files
removeAllSame: check {
  all fs, fs1, fs2: FileSystem, f: File |
    remove[fs, fs1, f] && removeAll[fs, fs2, f] => fs1.live = fs2.live
} for 5