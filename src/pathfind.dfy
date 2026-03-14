include "utils.dfy"
include "visibility.dfy"
include "a_star.dfy"

module Pathfind {
  import opened Utils
  import opened Visibility
  import opened AStar

  // Driver method that combines the above methods to find the optimal path for an agent to reach the best visible goal in a grid environment.
  method pathfind(grid: Grid, rectangles: array<Rectangle>, agent_position: Point, value_function: Cell -> real) returns (visible: array2<bool>, path: seq<Point>)
    requires ValidPoint(agent_position, grid)
    requires forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)
    requires RectanglesMatchGrid(rectangles, grid)
    ensures visible.Length0 == grid.Length0 && visible.Length1 == grid.Length1
  {
    visible := CalculateFOV(grid, rectangles, agent_position);
    var goals := GetGoals(grid, visible, value_function);
    path := A_Star(grid, agent_position, goals);
  }

  method GetGoals(grid: Grid, visible: array2<bool>, value_function: Cell -> real)
    returns (visible_goals: seq<Point>)
    requires grid.Length0 == visible.Length0 && grid.Length1 == visible.Length1
  {
    visible_goals := [];
    for x := 0 to grid.Length0 {
      for y := 0 to grid.Length1{
        var c := grid[x, y];
        // A cell is a viable goal if it's visible and has a positive value according to the value function.
        if visible[x, y] && value_function(c) > 0.0 {
          visible_goals := visible_goals + [Point(x, y)];
        }
      }
    }
  }
}