module Utils{
  datatype Point = Point(x: int, y: int)
  datatype Rectangle = Rectangle(minX: int, minY: int, maxX: int, maxY: int)

  predicate ValidPoint<T>(p: Point, grid: array2<T>) { 0 <= p.x < grid.Length0 && 0 <= p.y < grid.Length1 }

  predicate ValidRectangle<T>(rectangle: Rectangle, grid: array2<T>)
  {
    0 <= rectangle.minX && rectangle.minX < rectangle.maxX && rectangle.maxX <= grid.Length0 &&
    0 <= rectangle.minY && rectangle.minY < rectangle.maxY && rectangle.maxY <= grid.Length1
  }

  function ManhattanDistance(p1: Point, p2: Point): int
  {
    var dx := p1.x - p2.x;
    var dy := p1.y - p2.y;
    (if dx >= 0 then dx else -dx) + (if dy >= 0 then dy else -dy)
  }

  method GetGoal<T>(grid: array2<T>, visible: array2<bool>, value_function: ((Point, Point, T) -> real), agent_position: Point)
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