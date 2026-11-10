// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

struct Point {
    uint64 x;
    int32 y;
}

contract MemoryStructs {
    struct Line {
        Point a;
        Point b;
        uint8 tag;
        bytes data;
        uint16[] ws;
        uint8[2] pair;
    }

    struct Two {
        uint64 u;
        uint64 v;
    }

    struct Packed {
        uint8 a;
        uint16 b;
    }

    enum Color { Red, Green }

    struct Paint {
        Color c;
        uint8 n;
    }

    Packed packed;
    Paint paint;

    function positional(uint64 x, int32 y) public pure returns (uint64, int32) {
        Point memory p = Point(x, y);
        return (p.x, p.y);
    }

    function named(uint64 x, int32 y) public pure returns (uint64, int32) {
        Point memory p = Point({y: y, x: x});
        p.x += 1;
        p.y -= 2;
        return (p.x, p.y);
    }

    function zeroed() public pure returns (uint64, int32, uint8, uint256, uint256, uint8) {
        Line memory l;
        return (l.a.x, l.b.y, l.tag, l.data.length, l.ws.length, l.pair[1]);
    }

    function aliasing(uint64 x) public pure returns (uint64, uint64, uint64) {
        Line memory l;
        l.a = Point(x, 1);
        l.b = l.a;
        l.b.x = x + 5;
        Point memory c = l.a;
        c.x += 1;
        return (l.a.x, l.b.x, c.x);
    }

    function array(uint256 n, uint256 i) public pure returns (uint64, int32, uint256) {
        Point[] memory ps = new Point[](n);
        ps[i].x = 9;
        Point memory q = ps[i];
        q.y = -4;
        return (ps[i].x, ps[i].y, ps.length);
    }

    function order(uint64 a) public pure returns (uint64, uint64) {
        uint64 c = a;
        Two memory t = Two({v: c++, u: c++});
        return (t.u, t.v);
    }

    function toStorage(uint8 a, uint16 b) public returns (uint8, uint16) {
        Packed memory p = Packed(a, b);
        packed = p;
        p.a = 1;
        return (packed.a, packed.b);
    }

    function fromStorage() public view returns (uint8, uint16) {
        Packed memory p = packed;
        return (p.a, p.b);
    }

    function snapshot(uint8 a) public returns (uint8, uint8) {
        Packed memory p = packed;
        packed.a = a;
        return (p.a, packed.a);
    }

    function paintCopy() public view returns (uint8) {
        Paint memory p = paint;
        return p.n;
    }

    function passing(uint64 x) public pure returns (uint64, uint64) {
        Point memory p = Point(x, 0);
        double(p);
        Point memory r = make(p.x);
        return (p.x, r.x);
    }

    function double(Point memory p) internal pure {
        p.x *= 2;
    }

    function make(uint64 x) internal pure returns (Point memory r) {
        r.x = x + 1;
    }

    function withBytes(uint8 t) public pure returns (uint256, uint8, uint16) {
        uint16[] memory ws = new uint16[](2);
        ws[1] = 300;
        uint8[2] memory pr;
        pr[0] = 5;
        Line memory l = Line(Point(1, 2), Point(3, 4), t, "abc", ws, pr);
        return (l.data.length, l.pair[0] + l.tag, l.ws[1]);
    }
}
