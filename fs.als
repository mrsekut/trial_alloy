//
// Alloy Tutorial
// - File System
// - https://alloytools.org/tutorials/online/frame-FS-1.html
// - https://scrapbox.io/mrsekut-p/Tutorial_for_Alloy_Analyzer_4.0を読む
//

// A file system object in the file system
abstract sig FSObject { }

// File system objects must be either directories or files.
sig File, Dir extends FSObject { }

// A File System
sig FileSystem {
  root: Dir,
  live: set FSObject, // live objects are reachable from the root?
  contents: Dir lone-> FSObject,
  parent: FSObject ->lone Dir
}{
  // root has no parent
  no root.parent
  // live objects are reachable from the root
  live in root.*contents
  // parent is the inverse of contents
  parent = ~contents
}

pred example { }

run example for exactly 1 FileSystem, 4 FSObject