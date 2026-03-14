include "pathfind.dfy"
include "utils.dfy"

import opened Utils
import opened Pathfind

method PrintVisibility(grid: array2<Cell>, visible: array2<bool>, source: Point)
  requires grid.Length0 == visible.Length0 && grid.Length1 == visible.Length1
{
  for i := 0 to grid.Length0 {
    for j := 0 to grid.Length1 {
      if i == source.x && j == source.y {
        print "S ";
      } else if visible[i, j] {
        var c := grid[i, j];
        print if c == Wall then "W " else "V ";
      } else {
        print "X ";
      }
    }
    print "\n";
  }
}

method Main()
{
  // for testing, maybe read in a file that describes the grid and the print out the visibility grid.
  var grid := new Cell[5,5];
  grid[0,0] := Empty; grid[0,1] := Empty; grid[0,2] := Wall;  grid[0,3] := Empty; grid[0,4] := Food;
  grid[1,0] := Empty; grid[1,1] := Wall;  grid[1,2] := Wall;  grid[1,3] := Empty; grid[1,4] := Empty;
  grid[2,0] := Empty; grid[2,1] := Empty; grid[2,2] := Empty; grid[2,3] := Empty; grid[2,4] := Empty;
  grid[3,0] := Food;  grid[3,1] := Empty; grid[3,2] := Wall;  grid[3,3] := Wall;  grid[3,4] := Empty;
  grid[4,0] := Empty; grid[4,1] := Empty; grid[4,2] := Empty; grid[4,3] := Empty; grid[4,4] := Food;
  var rectangles := ExtractWallRectangles(grid);

  var agent_position := Point(0, 4);
  var value_function := (c: Cell) => if c == Food then 1.0 else 0.0;
  var visible, path := pathfind(grid, rectangles, agent_position, value_function);

  PrintVisibility(grid, visible, agent_position);
}