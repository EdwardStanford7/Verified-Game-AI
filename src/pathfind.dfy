include "utils.dfy"
include "visibility.dfy"
include "a_star.dfy"

module Pathfind {
  import opened Utils
  import opened Visibility
  import opened AStar

  // Driver method that combines the above methods to find the optimal path for an agent to reach the best visible goal in a grid environment.
  method pathfind(grid: Grid, rectangles: array<Rectangle>, agent_position: Point, value_function: (Point, Point, Cell) -> real) returns (visible: array2<bool>, path: seq<Point>)
    requires ValidPoint(agent_position, grid)
    requires forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)
    ensures visible.Length0 == grid.Length0 && visible.Length1 == grid.Length1
    ensures forall i :: 0 <= i < |path| ==> ValidPoint(path[i], grid)
  {
    visible := CalculateFOV(grid, rectangles, agent_position);
    var goal := GetGoal(grid, visible, value_function, agent_position);
    path := A_Star(grid, agent_position, goal);
  }

  method GetGoal(grid: Grid, visible: array2<bool>, value_function: ((Point, Point, Cell) -> real), agent_position: Point)
    returns (goal: Point)
    requires grid.Length0 == visible.Length0 && grid.Length1 == visible.Length1
  {
    goal := agent_position; // Default to current position if no visible cells have value > 0.

    // Find the best value among visible cells.
    var best_value := 0.0;
    var distance := 0;

    for x := 0 to grid.Length0 {
      for y := 0 to grid.Length1 {
        if visible[x, y] {
          var value := value_function(agent_position, Point(x, y), grid[x, y]);
          if value > best_value {
            best_value := value;
            goal := Point(x, y);
          }
        }
      }
    }
  }
}