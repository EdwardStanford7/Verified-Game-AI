include "utils.dfy"
include "visibility.dfy"
include "a_star.dfy"

module Pathfind {
  import opened Utils
  import opened Visibility
  import opened AStar

  // Driver method that combines the above methods to find the optimal path for an agent to reach the best visible goal in a grid environment.
  method pathfind(grid: Grid, rectangles: array<Rectangle>, agent_position: Point, value_function: Cell -> real) returns (path: seq<Point>)
    requires ValidPoint(agent_position, grid)
    requires forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)
    requires RectanglesMatchGrid(rectangles, grid)
  {
    var visible_goals := GetVisibleGoals(grid, rectangles, agent_position, value_function);
    path := A_Star(grid, agent_position, visible_goals);
  }
}