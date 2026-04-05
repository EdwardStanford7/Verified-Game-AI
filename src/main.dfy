include "pathfind.dfy"

import opened Utils
import opened Pathfind

datatype Cell = Empty | Low | High | Food

method PrintGrid(grid: array2<Cell>)
{
  for i := 0 to grid.Length0 {
    for j := 0 to grid.Length1 {
      var c := grid[i, j];
      print if c == High then "H " else if c == Low then "L " else if c == Food then "F " else ". ";
    }
    print "\n";
  }
}

method PrintPath(grid: array2<Cell>, visible: array2<bool>, path: seq<Point>, agent_position: Point)
  requires grid.Length0 == visible.Length0 && grid.Length1 == visible.Length1
  requires forall i :: 0 <= i < |path| ==> ValidPoint(path[i], grid)
{
  var print_grid := new string[grid.Length0, grid.Length1] ;

  for i := 0 to grid.Length0 {
    for j := 0 to grid.Length1 {
      if i == agent_position.x && j == agent_position.y {
        print_grid[i, j] := "A ";
      } else if visible[i, j] {
        var c := grid[i, j];
        print_grid[i, j] := if c == High then "H " else if c == Low then "L " else if c == Food then "F " else ". ";
      } else {
        print_grid[i, j] := "  ";
      }
    }
  }

  for k := 0 to |path| {
    if k == 0 || k == |path| - 1 {
      continue;
    }
    var p := path[k];
    if !visible[p.x, p.y] {
      print "ERROR: path includes non-visible cell at (" ;
      print p.x ;
      print ", " ;
      print p.y ;
      print")\n";
    }
    print_grid[p.x, p.y] := "@ ";
  }

  for i := 0 to print_grid.Length0 {
    for j := 0 to print_grid.Length1 {
      print print_grid[i, j];
    }
    print "\n";
  }
}

method Main()
{
  // Test case: 25x25 grid with walls forming a cross in the middle and food in the corners and a few other places, agent starts in the top left quadrant. This should test visibility around corners and through narrow gaps as well as pathfinding around walls to reach goals.
  var grid := new Cell[25,25] ((i, j) => Empty);

  // Place some vision blocking walls
  for i := 5 to 10 {
    grid[5,i] := High;
    grid[i,5] := High;
    grid[19,i] := High;
    grid[i,19] := Low;
  }

  // Place some pathing obstacles
  for i := 12 to 17{
    grid[i, 8] := High;
    grid[7, i] := Low;
  }

  // Some goals to pathfind to.
  grid[4,16]:= Food;
  grid[15,4]:= Food;
  grid[20,20]:= Food;

  print "Initial Grid:\n";
  PrintGrid(grid);

  var visibility_blocking := (c: Cell) => c == High;
  var traversable := (c: Cell) => c != High && c != Low;
  var value_function := (agent_pos: Point, target_pos: Point, cell: Cell) => (if cell == Food then 1.0 else 0.0) / (ManhattanDistance(agent_pos, target_pos) + 1) as real; // Preference for closer goals if multiple visible.

  var pf := new Pathfinder<Cell>(grid, visibility_blocking, traversable);
  var start := Utils.Point(12, 12);
  var path, visible := pf.FindPath(start, value_function);

  print "\nPath to Best Visible Goal:\n";
  PrintPath(grid, visible, path, start);
}
