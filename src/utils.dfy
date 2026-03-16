module Utils{
  datatype Point = Point(x: int, y: int)
  datatype Cell = Empty | Wall | Food
  type Grid = array2<Cell>
  datatype Rectangle = Rectangle(minX: int, minY: int, maxX: int, maxY: int)

  predicate ValidPoint(p: Point, grid: Grid) { 0 <= p.x < grid.Length0 && 0 <= p.y < grid.Length1 }

  predicate ValidRectangle(rectangle: Rectangle, grid: Grid)
  {
    0 <= rectangle.minX && rectangle.minX < rectangle.maxX && rectangle.maxX <= grid.Length0 &&
    0 <= rectangle.minY && rectangle.minY < rectangle.maxY && rectangle.maxY <= grid.Length1
  }

  // Calculate the Manhattan distance between two points.
  function ManhattanDistance(p1: Point, p2: Point): int
  {
    var dx := p1.x - p2.x;
    var dy := p1.y - p2.y;
    (if dx >= 0 then dx else -dx) + (if dy >= 0 then dy else -dy)
  }

  // Call once during initialization to extract rectangles from the grid then use those rectangles for all calls to pathfind function.
  method ExtractWallRectangles(grid: Grid) returns (rectangles: array<Rectangle>)
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
        if grid[x, y] == Wall && !visited[x, y] {

          // Determine width
          var x_size := 0;
          while x + x_size < grid.Length0 && grid[x + x_size, y] == Wall && !visited[x + x_size, y]
            invariant x + x_size <= grid.Length0
          {
            x_size := x_size + 1;
          }

          // Determine height
          var y_size := 1;
          while y + y_size < grid.Length1 && forall xx {:trigger grid[xx, y + y_size]} :: x <= xx < x + x_size ==> grid[xx, y + y_size] == Wall && !visited[xx, y + y_size]
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