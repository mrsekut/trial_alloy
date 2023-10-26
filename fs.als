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

pred example { }

run example for exactly 1 FileSystem, 4 FSObject
