include "pathfind.dfy"
include "utils.dfy"

import opened Utils
import opened Pathfind

method PrintVisibility(grid: array2<Cell>, visible: array2<bool>, agent_position: Point)
  requires grid.Length0 == visible.Length0 && grid.Length1 == visible.Length1
{
  for i := 0 to grid.Length0 {
    for j := 0 to grid.Length1 {
      if i == agent_position.x && j == agent_position.y {
        print "A ";
      } else if visible[i, j] {
        var c := grid[i, j];
        print if c == Wall then "# " else ". ";
      } else {
        print "  ";
      }
    }
    print "\n";
  }
}

method PrintRectangles(rectangles: array<Rectangle>, grid: Grid)
  requires grid.Length0 == 25 && grid.Length1 == 25
  requires forall i :: 0 <= i < rectangles.Length ==> ValidRectangle(rectangles[i], grid)
{
  var print_grid := new int[25,25] ((i, j) => 0);

  for i := 0 to rectangles.Length {
    for x := rectangles[i].minX to rectangles[i].maxX {
      for y := rectangles[i].minY to rectangles[i].maxY {
        if print_grid[x, y] == 0 {
          print_grid[x, y] := i + 1;
        }else{
          print "ERROR OVERLAPPING RECTANGLE\n";
        }
      }
    }
  }

  for i := 0 to print_grid.Length0 {
    for j := 0 to print_grid.Length1 {
      if print_grid[i, j] == 0 {
        print "  ";
      } else {
        print print_grid[i, j];
        print " ";
      }
    }
    print "\n";
  }
}

method PrintGrid(grid: Grid)
{
  for i := 0 to grid.Length0 {
    for j := 0 to grid.Length1 {
      var c := grid[i, j];
      print if c == Wall then "# " else if c == Food then "F " else ". ";
    }
    print "\n";
  }
}

method Main()
{
  // Test case: 25x25 grid with walls forming a cross in the middle and food in the corners and a few other places, agent starts in the top left quadrant. This should test visibility around corners and through narrow gaps as well as pathfinding around walls to reach goals.
  var grid := new Cell[25,25] ((i, j) => Empty);

  // Place some walls
  for i := 5 to 10 {
    grid[5,i] := Wall;
    grid[i,5] := Wall;
    grid[19,i] := Wall;
    grid[i,19] := Wall;
  }

  print "Initial Grid:\n";
  PrintGrid(grid);

  var rectangles := ExtractWallRectangles(grid);

  print "\nExtracted Rectangles:\n";
  PrintRectangles(rectangles, grid);

  var agent_position := Point(0, 4);
  var value_function := (c: Cell) => if c == Food then 1.0 else 0.0;
  var visible, path := pathfind(grid, rectangles, agent_position, value_function);

  print "\nVisibility from Agent Position:\n";
  PrintVisibility(grid, visible, agent_position);
}