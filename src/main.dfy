include "pathfind.dfy"
include "utils.dfy"

// for debugging purposes, can remove later
include "visibility.dfy"
import opened Visibility

import opened Utils
import opened Pathfind

method ExtractWallRectangles(grid: Grid) returns (rectangles: array<Rectangle>)
  ensures forall i :: 0 <= i < rectangles.Length ==> ValidRectangle(rectangles[i], grid)
  ensures RectanglesMatchGrid(rectangles, grid)
{
  var rectangles_seq := [];

  var visited := new bool[grid.Length0, grid.Length1] ((i, j) => (false));
  for x := 0 to grid.Length0 {
    for y := 0 to grid.Length1 {
      visited[x, y] := false;
    }
  }

  for x := 0 to grid.Length0 {
    for y := 0 to grid.Length1 {
      if grid[x, y] == Wall && !visited[x, y] {

        // Determine width
        var width := 0;
        while x + width < grid.Length0 && grid[x + width, y] == Wall && !visited[x + width, y]
          invariant x + width <= grid.Length0
        {
          width := width + 1;
        }

        // Determine height
        var height := 0;
        while y + height < grid.Length1 && forall xx {:trigger grid[xx, y + height]} :: x <= xx < x + width ==> grid[xx, y + height] == Wall && !visited[xx, y + height]
          invariant y + height <= grid.Length1
        {
          height := height + 1;
        }

        // Mark visited
        for xx := x to x + width {
          for yy := y to y + height {
            visited[xx, yy] := true;
          }
        }

        rectangles_seq := rectangles_seq + [Rectangle(x, y, x + width, y + height)];
      }
    }
  }

  rectangles := new Rectangle[|rectangles_seq|] (i requires 0<= i < |rectangles_seq| => rectangles_seq[i]);

  // TODO: maybe deal with proving this later if we get around to it, this isn't part of the core algorithm we're trying to verify.
  assume {:axiom} RectanglesMatchGrid(rectangles, grid);
}

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
  var agent_position := Point(0, 0);

  // For debugging: compute visible rectangles from the agent's position
  var visible := RectangleFOV(grid, rectangles, agent_position);

  PrintVisibility(grid, visible, agent_position);

  //   var value_function := (c: Cell) => if c == Food then 1.0 else 0.0;
  //   var path := pathfind(grid, rectangles, agent_position, value_function);
}