include "utils.dfy"
include "visibility.dfy"
include "a_star.dfy"

module Pathfind {
  import opened Utils
  import opened Visibility
  import opened AStar

  // Driver method that combines the above methods to find the optimal path for an agent to reach the best visible goal in a grid environment.
  method pathfind<T>(grid: array2<T>, rectangles: array<Rectangle>, agent_position: Point, value: (Point, Point, T) -> real, traversable: T -> bool)  returns (visible: array2<bool>, path: seq<Point>)
    requires ValidPoint(agent_position, grid)
    requires forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)
    ensures visible.Length0 == grid.Length0 && visible.Length1 == grid.Length1
    ensures forall i :: 0 <= i < |path| ==> ValidPoint(path[i], grid)
  {
    visible := CalculateFOV(grid, rectangles, agent_position);
    var goal := GetGoal(grid, visible, value, agent_position);
    path := A_Star(grid, agent_position, goal, traversable);
  }

  // Call once during initialization to extract rectangles from the grid then use those rectangles for all calls to pathfind function.
  method ExtractBlockingRectangles<T>(grid: array2<T>, visibility_blocking: T -> bool) returns (rectangles: array<Rectangle>)
    ensures forall i :: 0 <= i < rectangles.Length ==> ValidRectangle(rectangles[i], grid)
  {
    var rectangles_seq := [];

    var visited := new bool[grid.Length0, grid.Length1] ((i, j) => (false));
    for x := 0 to grid.Length0 {
      for y := 0 to grid.Length1 {
        visited[x, y] := false;
      }
    }

    for x := 0 to grid.Length0
      invariant forall r :: r in rectangles_seq ==> ValidRectangle(r, grid)
    {
      for y := 0 to grid.Length1
        invariant forall r :: r in rectangles_seq ==> ValidRectangle(r, grid)
      {
        if visibility_blocking(grid[x, y]) && !visited[x, y] {

          // Determine width
          var x_size := 0;
          while x + x_size < grid.Length0 && visibility_blocking(grid[x + x_size, y]) && !visited[x + x_size, y]
            invariant x + x_size <= grid.Length0
          {
            x_size := x_size + 1;
          }

          // Determine height
          var y_size := 1;
          while y + y_size < grid.Length1 && forall xx {:trigger grid[xx, y + y_size]} :: x <= xx < x + x_size ==> visibility_blocking(grid[xx, y + y_size]) && !visited[xx, y + y_size]
            invariant y + y_size <= grid.Length1
          {
            y_size := y_size + 1;
          }

          // Mark visited
          for xx := x to x + x_size {
            for yy := y to y + y_size {
              visited[xx, yy] := true;
            }
          }

          rectangles_seq := rectangles_seq + [Rectangle(x, y, x + x_size, y + y_size)];
        }
      }
    }

    rectangles := new Rectangle[|rectangles_seq|] (i requires 0<= i < |rectangles_seq| => rectangles_seq[i]);
  }
}