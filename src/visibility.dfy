// ----------------------------------------------------------------------------------
// array2<T>-based visibility (Rectangle-Based FOV) from:
//   Evan R.M. Debenham and Roberto Solis-Oba,
//   "New Algorithms for Computing Field of Vision over 2D array2<T>s" (2020)
// https://aircconline.com/csit/papers/vol10/csit101801.pdf
//
// Notes:
// We have only implemented base rectangle FOV.
// Didn't implement the quadtree or FOV update optimizations.
//
// Coordinate convention:
// All geometric ray tests use the "doubling trick": every grid coordinate is
// multiplied by 2 so that the center of cell (x,y) sits at the integer point
// (2x+1, 2y+1), and every cell corner sits at an even integer point.  This
// lets us shoot rays from the exact center of the source cell using only
// integer arithmetic throughout.
// ----------------------------------------------------------------------------------

include "utils.dfy"
module Visibility {
  import opened Utils

  // ── Doubled-coordinate helpers ─────────────────────────────────────────────────

  // Center of cell p in the doubled coordinate space.
  // Cell (x,y) spans [2x, 2x+2] × [2y, 2y+2], so its center is (2x+1, 2y+1).
  function CellCenterDoubled(p: Point): Point {
    Point(2 * p.x + 1, 2 * p.y + 1)
  }

  // Rectangle in doubled coordinate space.
  // Grid rectangle [minX, maxX) × [minY, maxY) becomes [2·minX, 2·maxX) × [2·minY, 2·maxY).
  function RectDoubled(r: Rectangle): Rectangle {
    Rectangle(2 * r.minX, 2 * r.minY, 2 * r.maxX, 2 * r.maxY)
  }

  // ── Topology helpers ───────────────────────────────────────────────────────────

  // Check if a point p is on the boundary of rectangle r (regular grid coords).
  function PointOnRectBoundary(p: Point, r: Rectangle): bool {
    p.x >= r.minX && p.x < r.maxX &&
    p.y >= r.minY && p.y < r.maxY &&
    (p.x == r.minX || p.x == r.maxX - 1 || p.y == r.minY || p.y == r.maxY - 1)
  }

  // ── Geometric primitives (operate in whatever integer coordinate space is passed in) ──

  // Check if the line segment from s to p intersects the open interior of rectangle r.
  // A ray that grazes the boundary without entering the interior is NOT a hit.
  method SegmentIntersectsRectInterior(s: Point, p: Point, r: Rectangle) returns (hit: bool)
  {
    hit := false;

    var tEnter: real := 0.0;
    var tExit:  real := 1.0;

    var dx: int := p.x - s.x;
    var dy: int := p.y - s.y;

    // X slab
    if dx == 0 {
      if !(s.x >= r.minX && s.x < r.maxX) { return; }
    } else {
      var tx1: real := (r.minX as real - s.x as real) / (dx as real);
      var tx2: real := (r.maxX as real - s.x as real) / (dx as real);
      var tMinX: real := if tx1 < tx2 then tx1 else tx2;
      var tMaxX: real := if tx1 > tx2 then tx1 else tx2;

      if tMinX > tEnter { tEnter := tMinX; }
      if tMaxX < tExit  { tExit  := tMaxX; }
      if tEnter >= tExit { return; }
    }

    // Y slab
    if dy == 0 {
      if !(s.y >= r.minY && s.y < r.maxY) { return; }
    } else {
      var ty1: real := (r.minY as real - s.y as real) / (dy as real);
      var ty2: real := (r.maxY as real - s.y as real) / (dy as real);
      var tMinY: real := if ty1 < ty2 then ty1 else ty2;
      var tMaxY: real := if ty1 > ty2 then ty1 else ty2;

      if tMinY > tEnter { tEnter := tMinY; }
      if tMaxY < tExit  { tExit  := tMaxY; }
      if tEnter >= tExit { return; }
    }

    // Clamp to the open segment (0, 1) — endpoints are not interior hits.
    var t0: real := if tEnter > 0.0 then tEnter else 0.0;
    var t1: real := if tExit  < 1.0 then tExit  else 1.0;

    if t0 < t1 { hit := true; }
  }

  // ── Rectangle extension ────────────────────────────────────────────────────────

  // If two rectangles share a side, cells just behind their join can be
  // incorrectly marked visible.  Extend `current` by one cell into any adjacent
  // rectangle that does not itself occlude the relevant corner point p.
  //
  // All geometric tests are performed in the doubled coordinate space so that
  // rays originate from the exact center of the source cell.
  method ExtendRectangleAtPoint<T>(
    grid: array2<T>,
    source: Point,
    rectangles: array<Rectangle>,
    idx: int,
    current: Rectangle,
    p: Point)
    returns (outR: Rectangle)
    requires ValidRectangle(current, grid)
    requires forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)
    ensures  ValidRectangle(outR, grid)
  {
    outR := current;

    var src := CellCenterDoubled(source);
    // p is a rectangle corner in regular grid coords; double it for the ray test.
    var p_d := Point(2 * p.x, 2 * p.y);

    for j := 0 to rectangles.Length
      invariant ValidRectangle(outR, grid)
    {
      if j != idx && PointOnRectBoundary(p, rectangles[j]) {
        var rect_d  := RectDoubled(rectangles[j]);
        var occludes := SegmentIntersectsRectInterior(src, p_d, rect_d);

        if !occludes {
          if      current.minX == rectangles[j].maxX {
            outR := Rectangle(current.minX - 1, current.minY, current.maxX,     current.maxY    );
          } else if current.maxX == rectangles[j].minX {
            outR := Rectangle(current.minX,     current.minY, current.maxX + 1, current.maxY    );
          } else if current.minY == rectangles[j].maxY {
            outR := Rectangle(current.minX,     current.minY - 1, current.maxX, current.maxY    );
          } else if current.maxY == rectangles[j].minY {
            outR := Rectangle(current.minX,     current.minY, current.maxX,     current.maxY + 1);
          }
        }
      }
    }
  }

  // Extend the rectangle at `idx` if needed so that it properly occludes its
  // two relevant (tangent) vertices, then return the extended rectangle.
  method ExtendRectangle<T>(
    grid: array2<T>,
    source: Point,
    rectangles: array<Rectangle>,
    idx: int)
    returns (rOut: Rectangle)
    requires 0 <= idx < rectangles.Length
    requires forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)
    ensures  ValidRectangle(rOut, grid)
  {
    rOut := rectangles[idx];
    var p1, p2 := RelevantVertices(source, rOut);
    rOut := ExtendRectangleAtPoint(grid, source, rectangles, idx, rOut, p1);
    rOut := ExtendRectangleAtPoint(grid, source, rectangles, idx, rOut, p2);
  }

  // ── Visibility queries ─────────────────────────────────────────────────────────

  // Return the two tangent (relevant) corners of `rectangle` as seen from `source`.
  // Relevant corners are the two visible corners with the greatest mutual distance.
  //
  // Visibility self-test uses doubled coordinates: source → cell center,
  // corners → even-coordinate grid points.  Return values are in regular grid
  // coords because callers use them for topology checks (PointOnRectBoundary).
  method RelevantVertices(source: Point, rectangle: Rectangle) returns (p1: Point, p2: Point)
  {
    var src := CellCenterDoubled(source);
    var dr  := RectDoubled(rectangle);

    // Regular-grid corners (for return / topology use).
    var corner1 := Point(rectangle.minX, rectangle.minY); // top-left
    var corner2 := Point(rectangle.maxX, rectangle.minY); // top-right
    var corner3 := Point(rectangle.minX, rectangle.maxY); // bottom-left
    var corner4 := Point(rectangle.maxX, rectangle.maxY); // bottom-right

    // Doubled-coord corners (for ray intersection tests).
    var corner1_d := Point(2 * rectangle.minX, 2 * rectangle.minY);
    var corner2_d := Point(2 * rectangle.maxX, 2 * rectangle.minY);
    var corner3_d := Point(2 * rectangle.minX, 2 * rectangle.maxY);
    var corner4_d := Point(2 * rectangle.maxX, 2 * rectangle.maxY);

    var c1_occluded := SegmentIntersectsRectInterior(src, corner1_d, dr);
    var c2_occluded := SegmentIntersectsRectInterior(src, corner2_d, dr);
    var c3_occluded := SegmentIntersectsRectInterior(src, corner3_d, dr);
    var c4_occluded := SegmentIntersectsRectInterior(src, corner4_d, dr);

    var visible_corners := [];
    if !c1_occluded { visible_corners := visible_corners + [corner1]; }
    if !c2_occluded { visible_corners := visible_corners + [corner2]; }
    if !c3_occluded { visible_corners := visible_corners + [corner3]; }
    if !c4_occluded { visible_corners := visible_corners + [corner4]; }

    // The farthest-apart pair of visible corners are the tangent vertices.
    var max_dist := -1;
    p1 := corner1; // dummy inits required by Dafny
    p2 := corner1;
    for i := 0 to |visible_corners| {
      for j := i + 1 to |visible_corners| {
        var d := ManhattanDistance(visible_corners[i], visible_corners[j]);
        if d > max_dist {
          max_dist := d;
          p1 := visible_corners[i];
          p2 := visible_corners[j];
        }
      }
    }
  }

  // Check whether cell (x, y) is occluded by rectangle r from `source`.
  // A cell is occluded when at least 3 of its 4 corners are blocked by r.
  //
  // Rays originate from the center of the source cell (doubled coords) and
  // terminate at the four corners of the target cell (also in doubled coords).
  method CellOccludedByRect(source: Point, x: int, y: int, r: Rectangle) returns (occluded: bool)
  {
    var src := CellCenterDoubled(source);
    var dr  := RectDoubled(r);

    // Corners of cell (x, y) in doubled coordinate space (all even).
    var c1 := Point(2 * x,     2 * y    );
    var c2 := Point(2 * x + 2, 2 * y    );
    var c3 := Point(2 * x,     2 * y + 2);
    var c4 := Point(2 * x + 2, 2 * y + 2);

    var h1 := SegmentIntersectsRectInterior(src, c1, dr);
    var h2 := SegmentIntersectsRectInterior(src, c2, dr);
    var h3 := SegmentIntersectsRectInterior(src, c3, dr);
    var h4 := SegmentIntersectsRectInterior(src, c4, dr);

    var num_occluded := 0;
    if h1 { num_occluded := num_occluded + 1; }
    if h2 { num_occluded := num_occluded + 1; }
    if h3 { num_occluded := num_occluded + 1; }
    if h4 { num_occluded := num_occluded + 1; }

    occluded := num_occluded >= 3;
  }

  // ── Main FOV entry point ───────────────────────────────────────────────────────

  // Given a grid, a list of opaque rectangles, and a source cell, compute which
  // cells are visible from `source`.
  method CalculateFOV<T>(grid: array2<T>, rectangles_in: array<Rectangle>, source: Point)
    returns (visible: array2<bool>)
    requires ValidPoint(source, grid)
    requires forall j :: 0 <= j < rectangles_in.Length ==> ValidRectangle(rectangles_in[j], grid)
    ensures  visible.Length0 == grid.Length0 && visible.Length1 == grid.Length1
  {
    var rectangles := new Rectangle[rectangles_in.Length](
                                    i requires 0 <= i < rectangles_in.Length reads rectangles_in => rectangles_in[i]);

    visible := new bool[grid.Length0, grid.Length1]((i, j) => true);

    for i := 0 to rectangles.Length
      invariant forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)
    {
      var r := ExtendRectangle(grid, source, rectangles, i);
      rectangles[i] := r;

      for x := 0 to grid.Length0
        // Dafny cannot infer that the inner loops do not modify `rectangles`.
        invariant forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)
      {
        for y := 0 to grid.Length1
          invariant forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)
        {
          if visible[x, y] {
            var occ := CellOccludedByRect(source, x, y, r);
            if occ { visible[x, y] := false; }
          }
        }
      }
    }

    visible[source.x, source.y] := true;
  }
}
