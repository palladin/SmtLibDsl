/-
  SmtLibDsl - Sokoban Original Levels

  The original 90 levels from Sokoban (1982) by Hiroyuki Imabayashi.
  Published by Thinking Rabbit, Japan.

  Legend:
    # - Wall
    @ - Player
    $ - Box
    . - Goal
    * - Box on goal
    + - Player on goal
    (space) - Floor
-/
import SmtLibDsl

namespace Sokoban.Levels

/-- A Sokoban level as raw string lines -/
structure LevelData where
  name : String
  lines : List String
deriving Repr

/-- Original Level 1 -/
def level1 : LevelData := {
  name := "Level 1"
  lines := [
    "    #####",
    "    #   #",
    "    #$  #",
    "  ###  $##",
    "  #  $ $ #",
    "### # ## #   ######",
    "#   # ## #####  ..#",
    "# $  $          ..#",
    "##### ### #@##  ..#",
    "    #     #########",
    "    #######"
  ]
}

/-- Original Level 2 -/
def level2 : LevelData := {
  name := "Level 2"
  lines := [
    "############",
    "#..  #     ###",
    "#..  # $  $  #",
    "#..  #$####  #",
    "#..    @ ##  #",
    "#..  # #  $ ##",
    "###### ##$ $ #",
    "  # $  $ $ $ #",
    "  #    #     #",
    "  ############"
  ]
}

/-- Original Level 3 -/
def level3 : LevelData := {
  name := "Level 3"
  lines := [
    "        ########",
    "        #     @#",
    "        # $#$ ##",
    "        # $  $#",
    "        ##$ $ #",
    "######### $ # ###",
    "#....  ## $  $  #",
    "##...    $  $   #",
    "#....  ##########",
    "########"
  ]
}

/-- Original Level 4 -/
def level4 : LevelData := {
  name := "Level 4"
  lines := [
    "           ########",
    "           #  ....#",
    "############  ....#",
    "#    #  $ $   ....#",
    "# $$$#$  $ #  ....#",
    "#  $     $ #  ....#",
    "# $$ #$ $ $########",
    "#  $ #     #",
    "## #########",
    "#    #    ##",
    "#     $   ##",
    "#  $$#$$  @#",
    "#    #    ##",
    "###########"
  ]
}

/-- Original Level 5 -/
def level5 : LevelData := {
  name := "Level 5"
  lines := [
    "        #####",
    "        #   #####",
    "        # #$##  #",
    "        #     $ #",
    "######### ###   #",
    "#....  ## $  $###",
    "#....    $ $$ ##",
    "#....  ##$  $ @#",
    "##########  $  #",
    "         # $ $ #",
    "         ### ###",
    "           #   #",
    "           #####"
  ]
}

/-- Original Level 6 -/
def level6 : LevelData := {
  name := "Level 6"
  lines := [
    "######  ###",
    "#..  # ##@##",
    "#..  ###   #",
    "#..     $$ #",
    "#..  # # $ #",
    "#..### # $ #",
    "#### $ #$  #",
    "   #  $# $ #",
    "   # $  $  #",
    "   #  ##   #",
    "   #########"
  ]
}

/-- Original Level 7 -/
def level7 : LevelData := {
  name := "Level 7"
  lines := [
    "       #####",
    " #######   ##",
    "## # @## $$ #",
    "#    $      #",
    "#  $  ###   #",
    "### #####$###",
    "# $  ### ..#",
    "# $ $ $ ...#",
    "#    ###...#",
    "# $$ # #...#",
    "#  ### #####",
    "####"
  ]
}

/-- Original Level 8 -/
def level8 : LevelData := {
  name := "Level 8"
  lines := [
    "  ####",
    "  #  ###########",
    "  #    $   $ $ #",
    "  # $# $ #  $  #",
    "  #  $ $  #    #",
    "### $# #  #### #",
    "#@#$ $ $  ##   #",
    "#    $ #$#   # #",
    "#   $    $ $ $ #",
    "#####  #########",
    "  #      #",
    "  #      #",
    "  #......#",
    "  #......#",
    "  #......#",
    "  ########"
  ]
}

/-- Original Level 9 -/
def level9 : LevelData := {
  name := "Level 9"
  lines := [
    "          #######",
    "          #  ...#",
    "      #####  ...#",
    "      #      . .#",
    "      #  ##  ...#",
    "      ## ##  ...#",
    "     ### ########",
    "     # $$$ ##",
    " #####  $ $ #####",
    "##   #$ $   #   #",
    "#@ $  $    $  $ #",
    "###### $$ $ #####",
    "     #      #",
    "     ########"
  ]
}

/-- Original Level 10 -/
def level10 : LevelData := {
  name := "Level 10"
  lines := [
    " ###  #############",
    "##@####       #   #",
    "# $$   $$  $ $ ...#",
    "#  $$$#    $  #...#",
    "# $   # $$ $$ #...#",
    "###   #  $    #...#",
    "#     # $ $ $ #...#",
    "#    ###### ###...#",
    "## #  #  $ $  #...#",
    "#  ## # $$ $ $##..#",
    "# ..# #  $      #.#",
    "# ..# # $$$ $$$ #.#",
    "##### #       # #.#",
    "    # ######### #.#",
    "    #           #.#",
    "    ###############"
  ]
}

/-- Microban Level 1 (beginner-friendly) -/
def microban1 : LevelData := {
  name := "Microban 1"
  lines := [
    "####",
    "# .#",
    "#  ###",
    "#*@  #",
    "#  $ #",
    "#  ###",
    "####"
  ]
}

/-- Microban Level 2 -/
def microban2 : LevelData := {
  name := "Microban 2"
  lines := [
    "######",
    "#    #",
    "# #@ #",
    "# $* #",
    "# .* #",
    "#    #",
    "######"
  ]
}

/-- Microban Level 3 -/
def microban3 : LevelData := {
  name := "Microban 3"
  lines := [
    "  ####",
    "###  ####",
    "#     $ #",
    "# #  #$ #",
    "# . .#@ #",
    "#########"
  ]
}

/-- Microban Level 4 -/
def microban4 : LevelData := {
  name := "Microban 4"
  lines := [
    "########",
    "#      #",
    "# .**$@#",
    "#      #",
    "#####  #",
    "    ####"
  ]
}

/-- Microban Level 5 -/
def microban5 : LevelData := {
  name := "Microban 5"
  lines := [
    " #######",
    " #     #",
    " # .$. #",
    "## $@$ #",
    "#  .$. #",
    "#      #",
    "########"
  ]
}

/-- Simple demo level -/
def demo1 : LevelData := {
  name := "Demo 1 (1 box)"
  lines := [
    "#####",
    "#@$.#",
    "#####"
  ]
}

/-- Simple demo level 2 -/
def demo2 : LevelData := {
  name := "Demo 2 (2 boxes)"
  lines := [
    "######",
    "#    #",
    "# $@.#",
    "#  $ #",
    "#  . #",
    "######"
  ]
}

/-- All available levels indexed by number -/
def allLevels : List LevelData := [
  demo1,       -- 1
  demo2,       -- 2
  microban1,   -- 3
  microban2,   -- 4
  microban3,   -- 5
  microban4,   -- 6
  microban5,   -- 7
  level1,      -- 8
  level2,      -- 9
  level3,      -- 10
  level4,      -- 11
  level5,      -- 12
  level6,      -- 13
  level7,      -- 14
  level8,      -- 15
  level9,      -- 16
  level10      -- 17
]

/-- Get level by number (1-indexed) -/
def getLevel (n : Nat) : Option LevelData :=
  if n > 0 then allLevels[n - 1]? else none

/-- Get total number of levels -/
def levelCount : Nat := allLevels.length

end Sokoban.Levels
