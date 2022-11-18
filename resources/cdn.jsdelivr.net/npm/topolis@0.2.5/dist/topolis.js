// topolis. See https://github.com/bjornharrtell/topolis
// Licenses:
// https://github.com/bjornharrtell/topolis/blob/master/LICENSE.txt

(function (global, factory) {
	typeof exports === 'object' && typeof module !== 'undefined' ? factory(exports) :
	typeof define === 'function' && define.amd ? define(['exports'], factory) :
	(factory((global.topolis = {})));
}(this, (function (exports) { 'use strict';

'use strict';

var index$1 = partialSort;

// Floyd-Rivest selection algorithm:
// Rearrange items so that all items in the [left, k] range are smaller than all items in (k, right];
// The k-th element will have the (k - left + 1)th smallest value in [left, right]

function partialSort(arr, k, left, right, compare) {
    left = left || 0;
    right = right || (arr.length - 1);
    compare = compare || defaultCompare;

    while (right > left) {
        if (right - left > 600) {
            var n = right - left + 1;
            var m = k - left + 1;
            var z = Math.log(n);
            var s = 0.5 * Math.exp(2 * z / 3);
            var sd = 0.5 * Math.sqrt(z * s * (n - s) / n) * (m - n / 2 < 0 ? -1 : 1);
            var newLeft = Math.max(left, Math.floor(k - m * s / n + sd));
            var newRight = Math.min(right, Math.floor(k + (n - m) * s / n + sd));
            partialSort(arr, k, newLeft, newRight, compare);
        }

        var t = arr[k];
        var i = left;
        var j = right;

        swap(arr, left, k);
        if (compare(arr[right], t) > 0) swap(arr, left, right);

        while (i < j) {
            swap(arr, i, j);
            i++;
            j--;
            while (compare(arr[i], t) < 0) i++;
            while (compare(arr[j], t) > 0) j--;
        }

        if (compare(arr[left], t) === 0) swap(arr, left, j);
        else {
            j++;
            swap(arr, j, right);
        }

        if (j <= k) left = j + 1;
        if (k <= j) right = j - 1;
    }
}

function swap(arr, i, j) {
    var tmp = arr[i];
    arr[i] = arr[j];
    arr[j] = tmp;
}

function defaultCompare(a, b) {
    return a < b ? -1 : a > b ? 1 : 0;
}

'use strict';

var index = rbush;



function rbush(maxEntries, format) {
    if (!(this instanceof rbush)) return new rbush(maxEntries, format);

    // max entries in a node is 9 by default; min node fill is 40% for best performance
    this._maxEntries = Math.max(4, maxEntries || 9);
    this._minEntries = Math.max(2, Math.ceil(this._maxEntries * 0.4));

    if (format) {
        this._initFormat(format);
    }

    this.clear();
}

rbush.prototype = {

    all: function () {
        return this._all(this.data, []);
    },

    search: function (bbox) {

        var node = this.data,
            result = [],
            toBBox = this.toBBox;

        if (!intersects(bbox, node)) return result;

        var nodesToSearch = [],
            i, len, child, childBBox;

        while (node) {
            for (i = 0, len = node.children.length; i < len; i++) {

                child = node.children[i];
                childBBox = node.leaf ? toBBox(child) : child;

                if (intersects(bbox, childBBox)) {
                    if (node.leaf) result.push(child);
                    else if (contains(bbox, childBBox)) this._all(child, result);
                    else nodesToSearch.push(child);
                }
            }
            node = nodesToSearch.pop();
        }

        return result;
    },

    collides: function (bbox) {

        var node = this.data,
            toBBox = this.toBBox;

        if (!intersects(bbox, node)) return false;

        var nodesToSearch = [],
            i, len, child, childBBox;

        while (node) {
            for (i = 0, len = node.children.length; i < len; i++) {

                child = node.children[i];
                childBBox = node.leaf ? toBBox(child) : child;

                if (intersects(bbox, childBBox)) {
                    if (node.leaf || contains(bbox, childBBox)) return true;
                    nodesToSearch.push(child);
                }
            }
            node = nodesToSearch.pop();
        }

        return false;
    },

    load: function (data) {
        if (!(data && data.length)) return this;

        if (data.length < this._minEntries) {
            for (var i = 0, len = data.length; i < len; i++) {
                this.insert(data[i]);
            }
            return this;
        }

        // recursively build the tree with the given data from stratch using OMT algorithm
        var node = this._build(data.slice(), 0, data.length - 1, 0);

        if (!this.data.children.length) {
            // save as is if tree is empty
            this.data = node;

        } else if (this.data.height === node.height) {
            // split root if trees have the same height
            this._splitRoot(this.data, node);

        } else {
            if (this.data.height < node.height) {
                // swap trees if inserted one is bigger
                var tmpNode = this.data;
                this.data = node;
                node = tmpNode;
            }

            // insert the small tree into the large tree at appropriate level
            this._insert(node, this.data.height - node.height - 1, true);
        }

        return this;
    },

    insert: function (item) {
        if (item) this._insert(item, this.data.height - 1);
        return this;
    },

    clear: function () {
        this.data = createNode([]);
        return this;
    },

    remove: function (item, equalsFn) {
        if (!item) return this;

        var node = this.data,
            bbox = this.toBBox(item),
            path = [],
            indexes = [],
            i, parent, index, goingUp;

        // depth-first iterative tree traversal
        while (node || path.length) {

            if (!node) { // go up
                node = path.pop();
                parent = path[path.length - 1];
                i = indexes.pop();
                goingUp = true;
            }

            if (node.leaf) { // check current node
                index = findItem(item, node.children, equalsFn);

                if (index !== -1) {
                    // item found, remove the item and condense tree upwards
                    node.children.splice(index, 1);
                    path.push(node);
                    this._condense(path);
                    return this;
                }
            }

            if (!goingUp && !node.leaf && contains(node, bbox)) { // go down
                path.push(node);
                indexes.push(i);
                i = 0;
                parent = node;
                node = node.children[0];

            } else if (parent) { // go right
                i++;
                node = parent.children[i];
                goingUp = false;

            } else node = null; // nothing found
        }

        return this;
    },

    toBBox: function (item) { return item; },

    compareMinX: compareNodeMinX,
    compareMinY: compareNodeMinY,

    toJSON: function () { return this.data; },

    fromJSON: function (data) {
        this.data = data;
        return this;
    },

    _all: function (node, result) {
        var nodesToSearch = [];
        while (node) {
            if (node.leaf) result.push.apply(result, node.children);
            else nodesToSearch.push.apply(nodesToSearch, node.children);

            node = nodesToSearch.pop();
        }
        return result;
    },

    _build: function (items, left, right, height) {

        var N = right - left + 1,
            M = this._maxEntries,
            node;

        if (N <= M) {
            // reached leaf level; return leaf
            node = createNode(items.slice(left, right + 1));
            calcBBox(node, this.toBBox);
            return node;
        }

        if (!height) {
            // target height of the bulk-loaded tree
            height = Math.ceil(Math.log(N) / Math.log(M));

            // target number of root entries to maximize storage utilization
            M = Math.ceil(N / Math.pow(M, height - 1));
        }

        node = createNode([]);
        node.leaf = false;
        node.height = height;

        // split the items into M mostly square tiles

        var N2 = Math.ceil(N / M),
            N1 = N2 * Math.ceil(Math.sqrt(M)),
            i, j, right2, right3;

        multiSelect(items, left, right, N1, this.compareMinX);

        for (i = left; i <= right; i += N1) {

            right2 = Math.min(i + N1 - 1, right);

            multiSelect(items, i, right2, N2, this.compareMinY);

            for (j = i; j <= right2; j += N2) {

                right3 = Math.min(j + N2 - 1, right2);

                // pack each entry recursively
                node.children.push(this._build(items, j, right3, height - 1));
            }
        }

        calcBBox(node, this.toBBox);

        return node;
    },

    _chooseSubtree: function (bbox, node, level, path) {

        var i, len, child, targetNode, area, enlargement, minArea, minEnlargement;

        while (true) {
            path.push(node);

            if (node.leaf || path.length - 1 === level) break;

            minArea = minEnlargement = Infinity;

            for (i = 0, len = node.children.length; i < len; i++) {
                child = node.children[i];
                area = bboxArea(child);
                enlargement = enlargedArea(bbox, child) - area;

                // choose entry with the least area enlargement
                if (enlargement < minEnlargement) {
                    minEnlargement = enlargement;
                    minArea = area < minArea ? area : minArea;
                    targetNode = child;

                } else if (enlargement === minEnlargement) {
                    // otherwise choose one with the smallest area
                    if (area < minArea) {
                        minArea = area;
                        targetNode = child;
                    }
                }
            }

            node = targetNode || node.children[0];
        }

        return node;
    },

    _insert: function (item, level, isNode) {

        var toBBox = this.toBBox,
            bbox = isNode ? item : toBBox(item),
            insertPath = [];

        // find the best node for accommodating the item, saving all nodes along the path too
        var node = this._chooseSubtree(bbox, this.data, level, insertPath);

        // put the item into the node
        node.children.push(item);
        extend(node, bbox);

        // split on node overflow; propagate upwards if necessary
        while (level >= 0) {
            if (insertPath[level].children.length > this._maxEntries) {
                this._split(insertPath, level);
                level--;
            } else break;
        }

        // adjust bboxes along the insertion path
        this._adjustParentBBoxes(bbox, insertPath, level);
    },

    // split overflowed node into two
    _split: function (insertPath, level) {

        var node = insertPath[level],
            M = node.children.length,
            m = this._minEntries;

        this._chooseSplitAxis(node, m, M);

        var splitIndex = this._chooseSplitIndex(node, m, M);

        var newNode = createNode(node.children.splice(splitIndex, node.children.length - splitIndex));
        newNode.height = node.height;
        newNode.leaf = node.leaf;

        calcBBox(node, this.toBBox);
        calcBBox(newNode, this.toBBox);

        if (level) insertPath[level - 1].children.push(newNode);
        else this._splitRoot(node, newNode);
    },

    _splitRoot: function (node, newNode) {
        // split root node
        this.data = createNode([node, newNode]);
        this.data.height = node.height + 1;
        this.data.leaf = false;
        calcBBox(this.data, this.toBBox);
    },

    _chooseSplitIndex: function (node, m, M) {

        var i, bbox1, bbox2, overlap, area, minOverlap, minArea, index;

        minOverlap = minArea = Infinity;

        for (i = m; i <= M - m; i++) {
            bbox1 = distBBox(node, 0, i, this.toBBox);
            bbox2 = distBBox(node, i, M, this.toBBox);

            overlap = intersectionArea(bbox1, bbox2);
            area = bboxArea(bbox1) + bboxArea(bbox2);

            // choose distribution with minimum overlap
            if (overlap < minOverlap) {
                minOverlap = overlap;
                index = i;

                minArea = area < minArea ? area : minArea;

            } else if (overlap === minOverlap) {
                // otherwise choose distribution with minimum area
                if (area < minArea) {
                    minArea = area;
                    index = i;
                }
            }
        }

        return index;
    },

    // sorts node children by the best axis for split
    _chooseSplitAxis: function (node, m, M) {

        var compareMinX = node.leaf ? this.compareMinX : compareNodeMinX,
            compareMinY = node.leaf ? this.compareMinY : compareNodeMinY,
            xMargin = this._allDistMargin(node, m, M, compareMinX),
            yMargin = this._allDistMargin(node, m, M, compareMinY);

        // if total distributions margin value is minimal for x, sort by minX,
        // otherwise it's already sorted by minY
        if (xMargin < yMargin) node.children.sort(compareMinX);
    },

    // total margin of all possible split distributions where each node is at least m full
    _allDistMargin: function (node, m, M, compare) {

        node.children.sort(compare);

        var toBBox = this.toBBox,
            leftBBox = distBBox(node, 0, m, toBBox),
            rightBBox = distBBox(node, M - m, M, toBBox),
            margin = bboxMargin(leftBBox) + bboxMargin(rightBBox),
            i, child;

        for (i = m; i < M - m; i++) {
            child = node.children[i];
            extend(leftBBox, node.leaf ? toBBox(child) : child);
            margin += bboxMargin(leftBBox);
        }

        for (i = M - m - 1; i >= m; i--) {
            child = node.children[i];
            extend(rightBBox, node.leaf ? toBBox(child) : child);
            margin += bboxMargin(rightBBox);
        }

        return margin;
    },

    _adjustParentBBoxes: function (bbox, path, level) {
        // adjust bboxes along the given tree path
        for (var i = level; i >= 0; i--) {
            extend(path[i], bbox);
        }
    },

    _condense: function (path) {
        // go through the path, removing empty nodes and updating bboxes
        for (var i = path.length - 1, siblings; i >= 0; i--) {
            if (path[i].children.length === 0) {
                if (i > 0) {
                    siblings = path[i - 1].children;
                    siblings.splice(siblings.indexOf(path[i]), 1);

                } else this.clear();

            } else calcBBox(path[i], this.toBBox);
        }
    },

    _initFormat: function (format) {
        // data format (minX, minY, maxX, maxY accessors)

        // uses eval-type function compilation instead of just accepting a toBBox function
        // because the algorithms are very sensitive to sorting functions performance,
        // so they should be dead simple and without inner calls

        var compareArr = ['return a', ' - b', ';'];

        this.compareMinX = new Function('a', 'b', compareArr.join(format[0]));
        this.compareMinY = new Function('a', 'b', compareArr.join(format[1]));

        this.toBBox = new Function('a',
            'return {minX: a' + format[0] +
            ', minY: a' + format[1] +
            ', maxX: a' + format[2] +
            ', maxY: a' + format[3] + '};');
    }
};

function findItem(item, items, equalsFn) {
    if (!equalsFn) return items.indexOf(item);

    for (var i = 0; i < items.length; i++) {
        if (equalsFn(item, items[i])) return i;
    }
    return -1;
}

// calculate node's bbox from bboxes of its children
function calcBBox(node, toBBox) {
    distBBox(node, 0, node.children.length, toBBox, node);
}

// min bounding rectangle of node children from k to p-1
function distBBox(node, k, p, toBBox, destNode) {
    if (!destNode) destNode = createNode(null);
    destNode.minX = Infinity;
    destNode.minY = Infinity;
    destNode.maxX = -Infinity;
    destNode.maxY = -Infinity;

    for (var i = k, child; i < p; i++) {
        child = node.children[i];
        extend(destNode, node.leaf ? toBBox(child) : child);
    }

    return destNode;
}

function extend(a, b) {
    a.minX = Math.min(a.minX, b.minX);
    a.minY = Math.min(a.minY, b.minY);
    a.maxX = Math.max(a.maxX, b.maxX);
    a.maxY = Math.max(a.maxY, b.maxY);
    return a;
}

function compareNodeMinX(a, b) { return a.minX - b.minX; }
function compareNodeMinY(a, b) { return a.minY - b.minY; }

function bboxArea(a)   { return (a.maxX - a.minX) * (a.maxY - a.minY); }
function bboxMargin(a) { return (a.maxX - a.minX) + (a.maxY - a.minY); }

function enlargedArea(a, b) {
    return (Math.max(b.maxX, a.maxX) - Math.min(b.minX, a.minX)) *
           (Math.max(b.maxY, a.maxY) - Math.min(b.minY, a.minY));
}

function intersectionArea(a, b) {
    var minX = Math.max(a.minX, b.minX),
        minY = Math.max(a.minY, b.minY),
        maxX = Math.min(a.maxX, b.maxX),
        maxY = Math.min(a.maxY, b.maxY);

    return Math.max(0, maxX - minX) *
           Math.max(0, maxY - minY);
}

function contains(a, b) {
    return a.minX <= b.minX &&
           a.minY <= b.minY &&
           b.maxX <= a.maxX &&
           b.maxY <= a.maxY;
}

function intersects(a, b) {
    return b.minX <= a.maxX &&
           b.minY <= a.maxY &&
           b.maxX >= a.minX &&
           b.maxY >= a.minY;
}

function createNode(children) {
    return {
        children: children,
        height: 1,
        leaf: true,
        minX: Infinity,
        minY: Infinity,
        maxX: -Infinity,
        maxY: -Infinity
    };
}

// sort an array so that items come in groups of n unsorted items, with groups sorted between each other;
// combines selection algorithm with binary divide & conquer approach

function multiSelect(arr, left, right, n, compare) {
    var stack = [left, right],
        mid;

    while (stack.length) {
        right = stack.pop();
        left = stack.pop();

        if (right - left <= n) continue;

        mid = left + Math.ceil((right - left) / n / 2) * n;
        index$1(arr, mid, left, right, compare);

        stack.push(left, mid, mid, right);
    }
}

var extend$1 = function (target, source) {
  for (let key in source) {
    if (source.hasOwnProperty(key)) target[key] = source[key];
  }
};

function NumberUtil() {}
extend$1(NumberUtil.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return NumberUtil;
	}
});
NumberUtil.equalsWithTolerance = function (x1, x2, tolerance) {
	return Math.abs(x1 - x2) <= tolerance;
};

function IllegalArgumentException () {}

function Double () {}
Double.isNaN = n => Number.isNaN(n);
Double.doubleToLongBits = n => n;
Double.longBitsToDouble = n => n;
Double.isInfinite = n => !Number.isFinite(n);
Double.MAX_VALUE = Number.MAX_VALUE;

function Comparable () {}

function Clonable () {}

function Comparator () {}

function Serializable () {}

function RuntimeException (message) {
  this.name = 'RuntimeException';
  this.message = message;
  this.stack = (new Error()).stack;
  Error.call(this, message);
}

RuntimeException.prototype = Object.create(Error.prototype);
RuntimeException.prototype.constructor = Error;

var inherits = function (c, p) {
  c.prototype = Object.create(p.prototype);
  c.prototype.constructor = c;
};

function AssertionFailedException() {
	if (arguments.length === 0) {
		RuntimeException.call(this);
	} else if (arguments.length === 1) {
		let message = arguments[0];
		RuntimeException.call(this, message);
	}
}
inherits(AssertionFailedException, RuntimeException);
extend$1(AssertionFailedException.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return AssertionFailedException;
	}
});

function Assert() {}
extend$1(Assert.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Assert;
	}
});
Assert.shouldNeverReachHere = function () {
	if (arguments.length === 0) {
		Assert.shouldNeverReachHere(null);
	} else if (arguments.length === 1) {
		let message = arguments[0];
		throw new AssertionFailedException("Should never reach here" + (message !== null ? ": " + message : ""));
	}
};
Assert.isTrue = function () {
	if (arguments.length === 1) {
		let assertion = arguments[0];
		Assert.isTrue(assertion, null);
	} else if (arguments.length === 2) {
		let assertion = arguments[0], message = arguments[1];
		if (!assertion) {
			if (message === null) {
				throw new AssertionFailedException();
			} else {
				throw new AssertionFailedException(message);
			}
		}
	}
};
Assert.equals = function () {
	if (arguments.length === 2) {
		let expectedValue = arguments[0], actualValue = arguments[1];
		Assert.equals(expectedValue, actualValue, null);
	} else if (arguments.length === 3) {
		let expectedValue = arguments[0], actualValue = arguments[1], message = arguments[2];
		if (!actualValue.equals(expectedValue)) {
			throw new AssertionFailedException("Expected " + expectedValue + " but encountered " + actualValue + (message !== null ? ": " + message : ""));
		}
	}
};

function Coordinate() {
	this.x = null;
	this.y = null;
	this.z = null;
	if (arguments.length === 0) {
		Coordinate.call(this, 0.0, 0.0);
	} else if (arguments.length === 1) {
		let c = arguments[0];
		Coordinate.call(this, c.x, c.y, c.z);
	} else if (arguments.length === 2) {
		let x = arguments[0], y = arguments[1];
		Coordinate.call(this, x, y, Coordinate.NULL_ORDINATE);
	} else if (arguments.length === 3) {
		let x = arguments[0], y = arguments[1], z = arguments[2];
		this.x = x;
		this.y = y;
		this.z = z;
	}
}
extend$1(Coordinate.prototype, {
	setOrdinate: function (ordinateIndex, value) {
		switch (ordinateIndex) {
			case Coordinate.X:
				this.x = value;
				break;
			case Coordinate.Y:
				this.y = value;
				break;
			case Coordinate.Z:
				this.z = value;
				break;
			default:
				throw new IllegalArgumentException("Invalid ordinate index: " + ordinateIndex);
		}
	},
	equals2D: function () {
		if (arguments.length === 1) {
			let other = arguments[0];
			if (this.x !== other.x) {
				return false;
			}
			if (this.y !== other.y) {
				return false;
			}
			return true;
		} else if (arguments.length === 2) {
			let c = arguments[0], tolerance = arguments[1];
			if (!NumberUtil.equalsWithTolerance(this.x, c.x, tolerance)) {
				return false;
			}
			if (!NumberUtil.equalsWithTolerance(this.y, c.y, tolerance)) {
				return false;
			}
			return true;
		}
	},
	getOrdinate: function (ordinateIndex) {
		switch (ordinateIndex) {
			case Coordinate.X:
				return this.x;
			case Coordinate.Y:
				return this.y;
			case Coordinate.Z:
				return this.z;
		}
		throw new IllegalArgumentException("Invalid ordinate index: " + ordinateIndex);
	},
	equals3D: function (other) {
		return this.x === other.x && this.y === other.y && (this.z === other.z || Double.isNaN(this.z) && Double.isNaN(other.z));
	},
	equals: function (other) {
		if (!(other instanceof Coordinate)) {
			return false;
		}
		return this.equals2D(other);
	},
	equalInZ: function (c, tolerance) {
		return NumberUtil.equalsWithTolerance(this.z, c.z, tolerance);
	},
	compareTo: function (o) {
		var other = o;
		if (this.x < other.x) return -1;
		if (this.x > other.x) return 1;
		if (this.y < other.y) return -1;
		if (this.y > other.y) return 1;
		return 0;
	},
	clone: function () {
		try {
			var coord = null;
			return coord;
		} catch (e) {
			if (e instanceof CloneNotSupportedException) {
				Assert.shouldNeverReachHere("this shouldn't happen because this class is Cloneable");
				return null;
			} else throw e;
		} finally {}
	},
	copy: function () {
		return new Coordinate(this);
	},
	toString: function () {
		return "(" + this.x + ", " + this.y + ", " + this.z + ")";
	},
	distance3D: function (c) {
		var dx = this.x - c.x;
		var dy = this.y - c.y;
		var dz = this.z - c.z;
		return Math.sqrt(dx * dx + dy * dy + dz * dz);
	},
	distance: function (c) {
		var dx = this.x - c.x;
		var dy = this.y - c.y;
		return Math.sqrt(dx * dx + dy * dy);
	},
	hashCode: function () {
		var result = 17;
		result = 37 * result + Coordinate.hashCode(this.x);
		result = 37 * result + Coordinate.hashCode(this.y);
		return result;
	},
	setCoordinate: function (other) {
		this.x = other.x;
		this.y = other.y;
		this.z = other.z;
	},
	interfaces_: function () {
		return [Comparable, Clonable, Serializable];
	},
	getClass: function () {
		return Coordinate;
	}
});
Coordinate.hashCode = function () {
	if (arguments.length === 1) {
		let x = arguments[0];
		var f = Double.doubleToLongBits(x);
		return Math.trunc(f ^ f >>> 32);
	}
};
function DimensionalComparator() {
	this.dimensionsToTest = 2;
	if (arguments.length === 0) {
		DimensionalComparator.call(this, 2);
	} else if (arguments.length === 1) {
		let dimensionsToTest = arguments[0];
		if (dimensionsToTest !== 2 && dimensionsToTest !== 3) throw new IllegalArgumentException("only 2 or 3 dimensions may be specified");
		this.dimensionsToTest = dimensionsToTest;
	}
}
extend$1(DimensionalComparator.prototype, {
	compare: function (o1, o2) {
		var c1 = o1;
		var c2 = o2;
		var compX = DimensionalComparator.compare(c1.x, c2.x);
		if (compX !== 0) return compX;
		var compY = DimensionalComparator.compare(c1.y, c2.y);
		if (compY !== 0) return compY;
		if (this.dimensionsToTest <= 2) return 0;
		var compZ = DimensionalComparator.compare(c1.z, c2.z);
		return compZ;
	},
	interfaces_: function () {
		return [Comparator];
	},
	getClass: function () {
		return DimensionalComparator;
	}
});
DimensionalComparator.compare = function (a, b) {
	if (a < b) return -1;
	if (a > b) return 1;
	if (Double.isNaN(a)) {
		if (Double.isNaN(b)) return 0;
		return -1;
	}
	if (Double.isNaN(b)) return 1;
	return 0;
};
Coordinate.DimensionalComparator = DimensionalComparator;
Coordinate.serialVersionUID = 6683108902428366910;
Coordinate.NULL_ORDINATE = Double.NaN;
Coordinate.X = 0;
Coordinate.Y = 1;
Coordinate.Z = 2;

var hasInterface = function (o, i) {
  return o.interfaces_ && o.interfaces_().indexOf(i) > -1
};

function CoordinateSequence() {}
extend$1(CoordinateSequence.prototype, {
	setOrdinate: function (index, ordinateIndex, value) {},
	size: function () {},
	getOrdinate: function (index, ordinateIndex) {},
	getCoordinate: function () {

	},
	getCoordinateCopy: function (i) {},
	getDimension: function () {},
	getX: function (index) {},
	clone: function () {},
	expandEnvelope: function (env) {},
	copy: function () {},
	getY: function (index) {},
	toCoordinateArray: function () {},
	interfaces_: function () {
		return [Clonable];
	},
	getClass: function () {
		return CoordinateSequence;
	}
});
CoordinateSequence.X = 0;
CoordinateSequence.Y = 1;
CoordinateSequence.Z = 2;
CoordinateSequence.M = 3;

function CoordinateSequenceFactory() {}
extend$1(CoordinateSequenceFactory.prototype, {
	create: function () {
		if (arguments.length === 1) {
			if (arguments[0] instanceof Array) {

			} else if (hasInterface(arguments[0], CoordinateSequence)) {

			}
		} else if (arguments.length === 2) {

		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return CoordinateSequenceFactory;
	}
});

function Location() {}
extend$1(Location.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Location;
	}
});
Location.toLocationSymbol = function (locationValue) {
	switch (locationValue) {
		case Location.EXTERIOR:
			return 'e';
		case Location.BOUNDARY:
			return 'b';
		case Location.INTERIOR:
			return 'i';
		case Location.NONE:
			return '-';
	}
	throw new IllegalArgumentException("Unknown location value: " + locationValue);
};
Location.INTERIOR = 0;
Location.BOUNDARY = 1;
Location.EXTERIOR = 2;
Location.NONE = -1;

function MathUtil() {}
extend$1(MathUtil.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return MathUtil;
	}
});
MathUtil.log10 = function (x) {
	var ln = Math.log(x);
	if (Double.isInfinite(ln)) return ln;
	if (Double.isNaN(ln)) return ln;
	return ln / MathUtil.LOG_10;
};
MathUtil.min = function (v1, v2, v3, v4) {
	var min = v1;
	if (v2 < min) min = v2;
	if (v3 < min) min = v3;
	if (v4 < min) min = v4;
	return min;
};
MathUtil.clamp = function () {
	if (typeof arguments[2] === "number" && (typeof arguments[0] === "number" && typeof arguments[1] === "number")) {
		let x = arguments[0], min = arguments[1], max = arguments[2];
		if (x < min) return min;
		if (x > max) return max;
		return x;
	} else if (Number.isInteger(arguments[2]) && (Number.isInteger(arguments[0]) && Number.isInteger(arguments[1]))) {
		let x = arguments[0], min = arguments[1], max = arguments[2];
		if (x < min) return min;
		if (x > max) return max;
		return x;
	}
};
MathUtil.wrap = function (index, max) {
	if (index < 0) {
		return max - -index % max;
	}
	return index % max;
};
MathUtil.max = function () {
	if (arguments.length === 3) {
		let v1 = arguments[0], v2 = arguments[1], v3 = arguments[2];
		var max = v1;
		if (v2 > max) max = v2;
		if (v3 > max) max = v3;
		return max;
	} else if (arguments.length === 4) {
		let v1 = arguments[0], v2 = arguments[1], v3 = arguments[2], v4 = arguments[3];
		var max = v1;
		if (v2 > max) max = v2;
		if (v3 > max) max = v3;
		if (v4 > max) max = v4;
		return max;
	}
};
MathUtil.average = function (x1, x2) {
	return (x1 + x2) / 2.0;
};
MathUtil.LOG_10 = Math.log(10);

function StringBuffer (str) {
  this.str = str;
}

StringBuffer.prototype.append = function (e) {
  this.str += e;
};

StringBuffer.prototype.setCharAt = function (i, c) {
  this.str = this.str.substr(0, i) + c + this.str.substr(i + 1);
};

StringBuffer.prototype.toString = function (e) {
  return this.str
};

function Integer (value) {
  this.value = value;
}

Integer.prototype.intValue = function () {
  return this.value
};
Integer.prototype.compareTo = function (o) {
  if (this.value < o) return -1
  if (this.value > o) return 1
  return 0
};

Integer.isNaN = n => Number.isNaN(n);

function Character () {}
Character.isWhitespace = c => ((c <= 32 && c >= 0) || c == 127);
Character.toUpperCase = c => c.toUpperCase();

function DD() {
	this.hi = 0.0;
	this.lo = 0.0;
	if (arguments.length === 0) {
		this.init(0.0);
	} else if (arguments.length === 1) {
		if (typeof arguments[0] === "number") {
			let x = arguments[0];
			this.init(x);
		} else if (arguments[0] instanceof DD) {
			let dd = arguments[0];
			this.init(dd);
		} else if (typeof arguments[0] === "string") {
			let str = arguments[0];
			DD.call(this, DD.parse(str));
		}
	} else if (arguments.length === 2) {
		let hi = arguments[0], lo = arguments[1];
		this.init(hi, lo);
	}
}
extend$1(DD.prototype, {
	le: function (y) {
		return this.hi < y.hi || this.hi === y.hi && this.lo <= y.lo;
	},
	extractSignificantDigits: function (insertDecimalPoint, magnitude) {
		var y = this.abs();
		var mag = DD.magnitude(y.hi);
		var scale = DD.TEN.pow(mag);
		y = y.divide(scale);
		if (y.gt(DD.TEN)) {
			y = y.divide(DD.TEN);
			mag += 1;
		} else if (y.lt(DD.ONE)) {
			y = y.multiply(DD.TEN);
			mag -= 1;
		}
		var decimalPointPos = mag + 1;
		var buf = new StringBuffer();
		var numDigits = DD.MAX_PRINT_DIGITS - 1;
		for (var i = 0; i <= numDigits; i++) {
			if (insertDecimalPoint && i === decimalPointPos) {
				buf.append('.');
			}
			var digit = Math.trunc(y.hi);
			if (digit < 0) {
				break;
			}
			var rebiasBy10 = false;
			var digitChar = 0;
			if (digit > 9) {
				rebiasBy10 = true;
				digitChar = '9';
			} else {
				digitChar = '0' + digit;
			}
			buf.append(digitChar);
			y = y.subtract(DD.valueOf(digit)).multiply(DD.TEN);
			if (rebiasBy10) y.selfAdd(DD.TEN);
			var continueExtractingDigits = true;
			var remMag = DD.magnitude(y.hi);
			if (remMag < 0 && Math.abs(remMag) >= numDigits - i) continueExtractingDigits = false;
			if (!continueExtractingDigits) break;
		}
		magnitude[0] = mag;
		return buf.toString();
	},
	sqr: function () {
		return this.multiply(this);
	},
	doubleValue: function () {
		return this.hi + this.lo;
	},
	subtract: function () {
		if (arguments[0] instanceof DD) {
			let y = arguments[0];
			return this.add(y.negate());
		} else if (typeof arguments[0] === "number") {
			let y = arguments[0];
			return this.add(-y);
		}
	},
	equals: function () {
		if (arguments.length === 1) {
			let y = arguments[0];
			return this.hi === y.hi && this.lo === y.lo;
		}
	},
	isZero: function () {
		return this.hi === 0.0 && this.lo === 0.0;
	},
	selfSubtract: function () {
		if (arguments[0] instanceof DD) {
			let y = arguments[0];
			if (this.isNaN()) return this;
			return this.selfAdd(-y.hi, -y.lo);
		} else if (typeof arguments[0] === "number") {
			let y = arguments[0];
			if (this.isNaN()) return this;
			return this.selfAdd(-y, 0.0);
		}
	},
	getSpecialNumberString: function () {
		if (this.isZero()) return "0.0";
		if (this.isNaN()) return "NaN ";
		return null;
	},
	min: function (x) {
		if (this.le(x)) {
			return this;
		} else {
			return x;
		}
	},
	selfDivide: function () {
		if (arguments.length === 1) {
			if (arguments[0] instanceof DD) {
				let y = arguments[0];
				return this.selfDivide(y.hi, y.lo);
			} else if (typeof arguments[0] === "number") {
				let y = arguments[0];
				return this.selfDivide(y, 0.0);
			}
		} else if (arguments.length === 2) {
			let yhi = arguments[0], ylo = arguments[1];
			var hc = null, tc = null, hy = null, ty = null, C = null, c = null, U = null, u = null;
			C = this.hi / yhi;
			c = DD.SPLIT * C;
			hc = c - C;
			u = DD.SPLIT * yhi;
			hc = c - hc;
			tc = C - hc;
			hy = u - yhi;
			U = C * yhi;
			hy = u - hy;
			ty = yhi - hy;
			u = hc * hy - U + hc * ty + tc * hy + tc * ty;
			c = (this.hi - U - u + this.lo - C * ylo) / yhi;
			u = C + c;
			this.hi = u;
			this.lo = C - u + c;
			return this;
		}
	},
	dump: function () {
		return "DD<" + this.hi + ", " + this.lo + ">";
	},
	divide: function () {
		if (arguments[0] instanceof DD) {
			let y = arguments[0];
			var hc = null, tc = null, hy = null, ty = null, C = null, c = null, U = null, u = null;
			C = this.hi / y.hi;
			c = DD.SPLIT * C;
			hc = c - C;
			u = DD.SPLIT * y.hi;
			hc = c - hc;
			tc = C - hc;
			hy = u - y.hi;
			U = C * y.hi;
			hy = u - hy;
			ty = y.hi - hy;
			u = hc * hy - U + hc * ty + tc * hy + tc * ty;
			c = (this.hi - U - u + this.lo - C * y.lo) / y.hi;
			u = C + c;
			var zhi = u;
			var zlo = C - u + c;
			return new DD(zhi, zlo);
		} else if (typeof arguments[0] === "number") {
			let y = arguments[0];
			if (Double.isNaN(y)) return DD.createNaN();
			return DD.copy(this).selfDivide(y, 0.0);
		}
	},
	ge: function (y) {
		return this.hi > y.hi || this.hi === y.hi && this.lo >= y.lo;
	},
	pow: function (exp) {
		if (exp === 0.0) return DD.valueOf(1.0);
		var r = new DD(this);
		var s = DD.valueOf(1.0);
		var n = Math.abs(exp);
		if (n > 1) {
			while (n > 0) {
				if (n % 2 === 1) {
					s.selfMultiply(r);
				}
				n /= 2;
				if (n > 0) r = r.sqr();
			}
		} else {
			s = r;
		}
		if (exp < 0) return s.reciprocal();
		return s;
	},
	ceil: function () {
		if (this.isNaN()) return DD.NaN;
		var fhi = Math.ceil(this.hi);
		var flo = 0.0;
		if (fhi === this.hi) {
			flo = Math.ceil(this.lo);
		}
		return new DD(fhi, flo);
	},
	compareTo: function (o) {
		var other = o;
		if (this.hi < other.hi) return -1;
		if (this.hi > other.hi) return 1;
		if (this.lo < other.lo) return -1;
		if (this.lo > other.lo) return 1;
		return 0;
	},
	rint: function () {
		if (this.isNaN()) return this;
		var plus5 = this.add(0.5);
		return plus5.floor();
	},
	setValue: function () {
		if (arguments[0] instanceof DD) {
			let value = arguments[0];
			this.init(value);
			return this;
		} else if (typeof arguments[0] === "number") {
			let value = arguments[0];
			this.init(value);
			return this;
		}
	},
	max: function (x) {
		if (this.ge(x)) {
			return this;
		} else {
			return x;
		}
	},
	sqrt: function () {
		if (this.isZero()) return DD.valueOf(0.0);
		if (this.isNegative()) {
			return DD.NaN;
		}
		var x = 1.0 / Math.sqrt(this.hi);
		var ax = this.hi * x;
		var axdd = DD.valueOf(ax);
		var diffSq = this.subtract(axdd.sqr());
		var d2 = diffSq.hi * (x * 0.5);
		return axdd.add(d2);
	},
	selfAdd: function () {
		if (arguments.length === 1) {
			if (arguments[0] instanceof DD) {
				let y = arguments[0];
				return this.selfAdd(y.hi, y.lo);
			} else if (typeof arguments[0] === "number") {
				let y = arguments[0];
				var H = null, h = null, S = null, s = null, e = null, f = null;
				S = this.hi + y;
				e = S - this.hi;
				s = S - e;
				s = y - e + (this.hi - s);
				f = s + this.lo;
				H = S + f;
				h = f + (S - H);
				this.hi = H + h;
				this.lo = h + (H - this.hi);
				return this;
			}
		} else if (arguments.length === 2) {
			let yhi = arguments[0], ylo = arguments[1];
			var H = null, h = null, T = null, t = null, S = null, s = null, e = null, f = null;
			S = this.hi + yhi;
			T = this.lo + ylo;
			e = S - this.hi;
			f = T - this.lo;
			s = S - e;
			t = T - f;
			s = yhi - e + (this.hi - s);
			t = ylo - f + (this.lo - t);
			e = s + T;
			H = S + e;
			h = e + (S - H);
			e = t + h;
			var zhi = H + e;
			var zlo = e + (H - zhi);
			this.hi = zhi;
			this.lo = zlo;
			return this;
		}
	},
	selfMultiply: function () {
		if (arguments.length === 1) {
			if (arguments[0] instanceof DD) {
				let y = arguments[0];
				return this.selfMultiply(y.hi, y.lo);
			} else if (typeof arguments[0] === "number") {
				let y = arguments[0];
				return this.selfMultiply(y, 0.0);
			}
		} else if (arguments.length === 2) {
			let yhi = arguments[0], ylo = arguments[1];
			var hx = null, tx = null, hy = null, ty = null, C = null, c = null;
			C = DD.SPLIT * this.hi;
			hx = C - this.hi;
			c = DD.SPLIT * yhi;
			hx = C - hx;
			tx = this.hi - hx;
			hy = c - yhi;
			C = this.hi * yhi;
			hy = c - hy;
			ty = yhi - hy;
			c = hx * hy - C + hx * ty + tx * hy + tx * ty + (this.hi * ylo + this.lo * yhi);
			var zhi = C + c;
			hx = C - zhi;
			var zlo = c + hx;
			this.hi = zhi;
			this.lo = zlo;
			return this;
		}
	},
	selfSqr: function () {
		return this.selfMultiply(this);
	},
	floor: function () {
		if (this.isNaN()) return DD.NaN;
		var fhi = Math.floor(this.hi);
		var flo = 0.0;
		if (fhi === this.hi) {
			flo = Math.floor(this.lo);
		}
		return new DD(fhi, flo);
	},
	negate: function () {
		if (this.isNaN()) return this;
		return new DD(-this.hi, -this.lo);
	},
	clone: function () {
		try {
			return null;
		} catch (ex) {
			if (ex instanceof CloneNotSupportedException) {
				return null;
			} else throw ex;
		} finally {}
	},
	multiply: function () {
		if (arguments[0] instanceof DD) {
			let y = arguments[0];
			if (y.isNaN()) return DD.createNaN();
			return DD.copy(this).selfMultiply(y);
		} else if (typeof arguments[0] === "number") {
			let y = arguments[0];
			if (Double.isNaN(y)) return DD.createNaN();
			return DD.copy(this).selfMultiply(y, 0.0);
		}
	},
	isNaN: function () {
		return Double.isNaN(this.hi);
	},
	intValue: function () {
		return Math.trunc(this.hi);
	},
	toString: function () {
		var mag = DD.magnitude(this.hi);
		if (mag >= -3 && mag <= 20) return this.toStandardNotation();
		return this.toSciNotation();
	},
	toStandardNotation: function () {
		var specialStr = this.getSpecialNumberString();
		if (specialStr !== null) return specialStr;
		var magnitude = new Array(1).fill(null);
		var sigDigits = this.extractSignificantDigits(true, magnitude);
		var decimalPointPos = magnitude[0] + 1;
		var num = sigDigits;
		if (sigDigits.charAt(0) === '.') {
			num = "0" + sigDigits;
		} else if (decimalPointPos < 0) {
			num = "0." + DD.stringOfChar('0', -decimalPointPos) + sigDigits;
		} else if (sigDigits.indexOf('.') === -1) {
			var numZeroes = decimalPointPos - sigDigits.length;
			var zeroes = DD.stringOfChar('0', numZeroes);
			num = sigDigits + zeroes + ".0";
		}
		if (this.isNegative()) return "-" + num;
		return num;
	},
	reciprocal: function () {
		var hc = null, tc = null, hy = null, ty = null, C = null, c = null, U = null, u = null;
		C = 1.0 / this.hi;
		c = DD.SPLIT * C;
		hc = c - C;
		u = DD.SPLIT * this.hi;
		hc = c - hc;
		tc = C - hc;
		hy = u - this.hi;
		U = C * this.hi;
		hy = u - hy;
		ty = this.hi - hy;
		u = hc * hy - U + hc * ty + tc * hy + tc * ty;
		c = (1.0 - U - u - C * this.lo) / this.hi;
		var zhi = C + c;
		var zlo = C - zhi + c;
		return new DD(zhi, zlo);
	},
	toSciNotation: function () {
		if (this.isZero()) return DD.SCI_NOT_ZERO;
		var specialStr = this.getSpecialNumberString();
		if (specialStr !== null) return specialStr;
		var magnitude = new Array(1).fill(null);
		var digits = this.extractSignificantDigits(false, magnitude);
		var expStr = DD.SCI_NOT_EXPONENT_CHAR + magnitude[0];
		if (digits.charAt(0) === '0') {
			throw new IllegalStateException("Found leading zero: " + digits);
		}
		var trailingDigits = "";
		if (digits.length > 1) trailingDigits = digits.substring(1);
		var digitsWithDecimal = digits.charAt(0) + "." + trailingDigits;
		if (this.isNegative()) return "-" + digitsWithDecimal + expStr;
		return digitsWithDecimal + expStr;
	},
	abs: function () {
		if (this.isNaN()) return DD.NaN;
		if (this.isNegative()) return this.negate();
		return new DD(this);
	},
	isPositive: function () {
		return this.hi > 0.0 || this.hi === 0.0 && this.lo > 0.0;
	},
	lt: function (y) {
		return this.hi < y.hi || this.hi === y.hi && this.lo < y.lo;
	},
	add: function () {
		if (arguments[0] instanceof DD) {
			let y = arguments[0];
			return DD.copy(this).selfAdd(y);
		} else if (typeof arguments[0] === "number") {
			let y = arguments[0];
			return DD.copy(this).selfAdd(y);
		}
	},
	init: function () {
		if (arguments.length === 1) {
			if (typeof arguments[0] === "number") {
				let x = arguments[0];
				this.hi = x;
				this.lo = 0.0;
			} else if (arguments[0] instanceof DD) {
				let dd = arguments[0];
				this.hi = dd.hi;
				this.lo = dd.lo;
			}
		} else if (arguments.length === 2) {
			let hi = arguments[0], lo = arguments[1];
			this.hi = hi;
			this.lo = lo;
		}
	},
	gt: function (y) {
		return this.hi > y.hi || this.hi === y.hi && this.lo > y.lo;
	},
	isNegative: function () {
		return this.hi < 0.0 || this.hi === 0.0 && this.lo < 0.0;
	},
	trunc: function () {
		if (this.isNaN()) return DD.NaN;
		if (this.isPositive()) return this.floor(); else return this.ceil();
	},
	signum: function () {
		if (this.hi > 0) return 1;
		if (this.hi < 0) return -1;
		if (this.lo > 0) return 1;
		if (this.lo < 0) return -1;
		return 0;
	},
	interfaces_: function () {
		return [Serializable, Comparable, Clonable];
	},
	getClass: function () {
		return DD;
	}
});
DD.sqr = function (x) {
	return DD.valueOf(x).selfMultiply(x);
};
DD.valueOf = function () {
	if (typeof arguments[0] === "string") {
		let str = arguments[0];
		return DD.parse(str);
	} else if (typeof arguments[0] === "number") {
		let x = arguments[0];
		return new DD(x);
	}
};
DD.sqrt = function (x) {
	return DD.valueOf(x).sqrt();
};
DD.parse = function (str) {
	var i = 0;
	var strlen = str.length;
	while (Character.isWhitespace(str.charAt(i))) i++;
	var isNegative = false;
	if (i < strlen) {
		var signCh = str.charAt(i);
		if (signCh === '-' || signCh === '+') {
			i++;
			if (signCh === '-') isNegative = true;
		}
	}
	var val = new DD();
	var numDigits = 0;
	var numBeforeDec = 0;
	var exp = 0;
	while (true) {
		if (i >= strlen) break;
		var ch = str.charAt(i);
		i++;
		if (Character.isDigit(ch)) {
			var d = ch - '0';
			val.selfMultiply(DD.TEN);
			val.selfAdd(d);
			numDigits++;
			continue;
		}
		if (ch === '.') {
			numBeforeDec = numDigits;
			continue;
		}
		if (ch === 'e' || ch === 'E') {
			var expStr = str.substring(i);
			try {
				exp = Integer.parseInt(expStr);
			} catch (ex) {
				if (ex instanceof NumberFormatException) {
					throw new NumberFormatException("Invalid exponent " + expStr + " in string " + str);
				} else throw ex;
			} finally {}
			break;
		}
		throw new NumberFormatException("Unexpected character '" + ch + "' at position " + i + " in string " + str);
	}
	var val2 = val;
	var numDecPlaces = numDigits - numBeforeDec - exp;
	if (numDecPlaces === 0) {
		val2 = val;
	} else if (numDecPlaces > 0) {
		var scale = DD.TEN.pow(numDecPlaces);
		val2 = val.divide(scale);
	} else if (numDecPlaces < 0) {
		var scale = DD.TEN.pow(-numDecPlaces);
		val2 = val.multiply(scale);
	}
	if (isNegative) {
		return val2.negate();
	}
	return val2;
};
DD.createNaN = function () {
	return new DD(Double.NaN, Double.NaN);
};
DD.copy = function (dd) {
	return new DD(dd);
};
DD.magnitude = function (x) {
	var xAbs = Math.abs(x);
	var xLog10 = Math.log(xAbs) / Math.log(10);
	var xMag = Math.trunc(Math.floor(xLog10));
	var xApprox = Math.pow(10, xMag);
	if (xApprox * 10 <= xAbs) xMag += 1;
	return xMag;
};
DD.stringOfChar = function (ch, len) {
	var buf = new StringBuffer();
	for (var i = 0; i < len; i++) {
		buf.append(ch);
	}
	return buf.toString();
};
DD.PI = new DD(3.141592653589793116e+00, 1.224646799147353207e-16);
DD.TWO_PI = new DD(6.283185307179586232e+00, 2.449293598294706414e-16);
DD.PI_2 = new DD(1.570796326794896558e+00, 6.123233995736766036e-17);
DD.E = new DD(2.718281828459045091e+00, 1.445646891729250158e-16);
DD.NaN = new DD(Double.NaN, Double.NaN);
DD.EPS = 1.23259516440783e-32;
DD.SPLIT = 134217729.0;
DD.MAX_PRINT_DIGITS = 32;
DD.TEN = DD.valueOf(10.0);
DD.ONE = DD.valueOf(1.0);
DD.SCI_NOT_EXPONENT_CHAR = "E";
DD.SCI_NOT_ZERO = "0.0E0";

function CGAlgorithmsDD() {}
extend$1(CGAlgorithmsDD.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return CGAlgorithmsDD;
	}
});
CGAlgorithmsDD.orientationIndex = function (p1, p2, q) {
	var index = CGAlgorithmsDD.orientationIndexFilter(p1, p2, q);
	if (index <= 1) return index;
	var dx1 = DD.valueOf(p2.x).selfAdd(-p1.x);
	var dy1 = DD.valueOf(p2.y).selfAdd(-p1.y);
	var dx2 = DD.valueOf(q.x).selfAdd(-p2.x);
	var dy2 = DD.valueOf(q.y).selfAdd(-p2.y);
	return dx1.selfMultiply(dy2).selfSubtract(dy1.selfMultiply(dx2)).signum();
};
CGAlgorithmsDD.signOfDet2x2 = function (x1, y1, x2, y2) {
	var det = x1.multiply(y2).selfSubtract(y1.multiply(x2));
	return det.signum();
};
CGAlgorithmsDD.intersection = function (p1, p2, q1, q2) {
	var denom1 = DD.valueOf(q2.y).selfSubtract(q1.y).selfMultiply(DD.valueOf(p2.x).selfSubtract(p1.x));
	var denom2 = DD.valueOf(q2.x).selfSubtract(q1.x).selfMultiply(DD.valueOf(p2.y).selfSubtract(p1.y));
	var denom = denom1.subtract(denom2);
	var numx1 = DD.valueOf(q2.x).selfSubtract(q1.x).selfMultiply(DD.valueOf(p1.y).selfSubtract(q1.y));
	var numx2 = DD.valueOf(q2.y).selfSubtract(q1.y).selfMultiply(DD.valueOf(p1.x).selfSubtract(q1.x));
	var numx = numx1.subtract(numx2);
	var fracP = numx.selfDivide(denom).doubleValue();
	var x = DD.valueOf(p1.x).selfAdd(DD.valueOf(p2.x).selfSubtract(p1.x).selfMultiply(fracP)).doubleValue();
	var numy1 = DD.valueOf(p2.x).selfSubtract(p1.x).selfMultiply(DD.valueOf(p1.y).selfSubtract(q1.y));
	var numy2 = DD.valueOf(p2.y).selfSubtract(p1.y).selfMultiply(DD.valueOf(p1.x).selfSubtract(q1.x));
	var numy = numy1.subtract(numy2);
	var fracQ = numy.selfDivide(denom).doubleValue();
	var y = DD.valueOf(q1.y).selfAdd(DD.valueOf(q2.y).selfSubtract(q1.y).selfMultiply(fracQ)).doubleValue();
	return new Coordinate(x, y);
};
CGAlgorithmsDD.orientationIndexFilter = function (pa, pb, pc) {
	var detsum = null;
	var detleft = (pa.x - pc.x) * (pb.y - pc.y);
	var detright = (pa.y - pc.y) * (pb.x - pc.x);
	var det = detleft - detright;
	if (detleft > 0.0) {
		if (detright <= 0.0) {
			return CGAlgorithmsDD.signum(det);
		} else {
			detsum = detleft + detright;
		}
	} else if (detleft < 0.0) {
		if (detright >= 0.0) {
			return CGAlgorithmsDD.signum(det);
		} else {
			detsum = -detleft - detright;
		}
	} else {
		return CGAlgorithmsDD.signum(det);
	}
	var errbound = CGAlgorithmsDD.DP_SAFE_EPSILON * detsum;
	if (det >= errbound || -det >= errbound) {
		return CGAlgorithmsDD.signum(det);
	}
	return 2;
};
CGAlgorithmsDD.signum = function (x) {
	if (x > 0) return 1;
	if (x < 0) return -1;
	return 0;
};
CGAlgorithmsDD.DP_SAFE_EPSILON = 1e-15;

function Exception () {}

function NotRepresentableException() {
	Exception.call(this, "Projective point not representable on the Cartesian plane.");
}
inherits(NotRepresentableException, Exception);
extend$1(NotRepresentableException.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return NotRepresentableException;
	}
});

function System () { }

System.arraycopy = (src, srcPos, dest, destPos, len) => {
  let c = 0;
  for (let i = srcPos; i < srcPos + len; i++) {
    dest[destPos + c] = src[i];
    c++;
  }
};

System.getProperty = (name) => {
  return {
    'line.separator': '\n'
  }[name]
};

function HCoordinate() {
	this.x = null;
	this.y = null;
	this.w = null;
	if (arguments.length === 0) {
		this.x = 0.0;
		this.y = 0.0;
		this.w = 1.0;
	} else if (arguments.length === 1) {
		let p = arguments[0];
		this.x = p.x;
		this.y = p.y;
		this.w = 1.0;
	} else if (arguments.length === 2) {
		if (typeof arguments[0] === "number" && typeof arguments[1] === "number") {
			let _x = arguments[0], _y = arguments[1];
			this.x = _x;
			this.y = _y;
			this.w = 1.0;
		} else if (arguments[0] instanceof HCoordinate && arguments[1] instanceof HCoordinate) {
			let p1 = arguments[0], p2 = arguments[1];
			this.x = p1.y * p2.w - p2.y * p1.w;
			this.y = p2.x * p1.w - p1.x * p2.w;
			this.w = p1.x * p2.y - p2.x * p1.y;
		} else if (arguments[0] instanceof Coordinate && arguments[1] instanceof Coordinate) {
			let p1 = arguments[0], p2 = arguments[1];
			this.x = p1.y - p2.y;
			this.y = p2.x - p1.x;
			this.w = p1.x * p2.y - p2.x * p1.y;
		}
	} else if (arguments.length === 3) {
		let _x = arguments[0], _y = arguments[1], _w = arguments[2];
		this.x = _x;
		this.y = _y;
		this.w = _w;
	} else if (arguments.length === 4) {
		let p1 = arguments[0], p2 = arguments[1], q1 = arguments[2], q2 = arguments[3];
		var px = p1.y - p2.y;
		var py = p2.x - p1.x;
		var pw = p1.x * p2.y - p2.x * p1.y;
		var qx = q1.y - q2.y;
		var qy = q2.x - q1.x;
		var qw = q1.x * q2.y - q2.x * q1.y;
		this.x = py * qw - qy * pw;
		this.y = qx * pw - px * qw;
		this.w = px * qy - qx * py;
	}
}
extend$1(HCoordinate.prototype, {
	getY: function () {
		var a = this.y / this.w;
		if (Double.isNaN(a) || Double.isInfinite(a)) {
			throw new NotRepresentableException();
		}
		return a;
	},
	getX: function () {
		var a = this.x / this.w;
		if (Double.isNaN(a) || Double.isInfinite(a)) {
			throw new NotRepresentableException();
		}
		return a;
	},
	getCoordinate: function () {
		var p = new Coordinate();
		p.x = this.getX();
		p.y = this.getY();
		return p;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return HCoordinate;
	}
});
HCoordinate.intersection = function (p1, p2, q1, q2) {
	var px = p1.y - p2.y;
	var py = p2.x - p1.x;
	var pw = p1.x * p2.y - p2.x * p1.y;
	var qx = q1.y - q2.y;
	var qy = q2.x - q1.x;
	var qw = q1.x * q2.y - q2.x * q1.y;
	var x = py * qw - qy * pw;
	var y = qx * pw - px * qw;
	var w = px * qy - qx * py;
	var xInt = x / w;
	var yInt = y / w;
	if (Double.isNaN(xInt) || (Double.isInfinite(xInt) || Double.isNaN(yInt)) || Double.isInfinite(yInt)) {
		throw new NotRepresentableException();
	}
	return new Coordinate(xInt, yInt);
};

function Envelope() {
	this.minx = null;
	this.maxx = null;
	this.miny = null;
	this.maxy = null;
	if (arguments.length === 0) {
		this.init();
	} else if (arguments.length === 1) {
		if (arguments[0] instanceof Coordinate) {
			let p = arguments[0];
			this.init(p.x, p.x, p.y, p.y);
		} else if (arguments[0] instanceof Envelope) {
			let env = arguments[0];
			this.init(env);
		}
	} else if (arguments.length === 2) {
		let p1 = arguments[0], p2 = arguments[1];
		this.init(p1.x, p2.x, p1.y, p2.y);
	} else if (arguments.length === 4) {
		let x1 = arguments[0], x2 = arguments[1], y1 = arguments[2], y2 = arguments[3];
		this.init(x1, x2, y1, y2);
	}
}
extend$1(Envelope.prototype, {
	getArea: function () {
		return this.getWidth() * this.getHeight();
	},
	equals: function (other) {
		if (!(other instanceof Envelope)) {
			return false;
		}
		var otherEnvelope = other;
		if (this.isNull()) {
			return otherEnvelope.isNull();
		}
		return this.maxx === otherEnvelope.getMaxX() && this.maxy === otherEnvelope.getMaxY() && this.minx === otherEnvelope.getMinX() && this.miny === otherEnvelope.getMinY();
	},
	intersection: function (env) {
		if (this.isNull() || env.isNull() || !this.intersects(env)) return new Envelope();
		var intMinX = this.minx > env.minx ? this.minx : env.minx;
		var intMinY = this.miny > env.miny ? this.miny : env.miny;
		var intMaxX = this.maxx < env.maxx ? this.maxx : env.maxx;
		var intMaxY = this.maxy < env.maxy ? this.maxy : env.maxy;
		return new Envelope(intMinX, intMaxX, intMinY, intMaxY);
	},
	isNull: function () {
		return this.maxx < this.minx;
	},
	getMaxX: function () {
		return this.maxx;
	},
	covers: function () {
		if (arguments.length === 1) {
			if (arguments[0] instanceof Coordinate) {
				let p = arguments[0];
				return this.covers(p.x, p.y);
			} else if (arguments[0] instanceof Envelope) {
				let other = arguments[0];
				if (this.isNull() || other.isNull()) {
					return false;
				}
				return other.getMinX() >= this.minx && other.getMaxX() <= this.maxx && other.getMinY() >= this.miny && other.getMaxY() <= this.maxy;
			}
		} else if (arguments.length === 2) {
			let x = arguments[0], y = arguments[1];
			if (this.isNull()) return false;
			return x >= this.minx && x <= this.maxx && y >= this.miny && y <= this.maxy;
		}
	},
	intersects: function () {
		if (arguments.length === 1) {
			if (arguments[0] instanceof Envelope) {
				let other = arguments[0];
				if (this.isNull() || other.isNull()) {
					return false;
				}
				return !(other.minx > this.maxx || other.maxx < this.minx || other.miny > this.maxy || other.maxy < this.miny);
			} else if (arguments[0] instanceof Coordinate) {
				let p = arguments[0];
				return this.intersects(p.x, p.y);
			}
		} else if (arguments.length === 2) {
			let x = arguments[0], y = arguments[1];
			if (this.isNull()) return false;
			return !(x > this.maxx || x < this.minx || y > this.maxy || y < this.miny);
		}
	},
	getMinY: function () {
		return this.miny;
	},
	getMinX: function () {
		return this.minx;
	},
	expandToInclude: function () {
		if (arguments.length === 1) {
			if (arguments[0] instanceof Coordinate) {
				let p = arguments[0];
				this.expandToInclude(p.x, p.y);
			} else if (arguments[0] instanceof Envelope) {
				let other = arguments[0];
				if (other.isNull()) {
					return null;
				}
				if (this.isNull()) {
					this.minx = other.getMinX();
					this.maxx = other.getMaxX();
					this.miny = other.getMinY();
					this.maxy = other.getMaxY();
				} else {
					if (other.minx < this.minx) {
						this.minx = other.minx;
					}
					if (other.maxx > this.maxx) {
						this.maxx = other.maxx;
					}
					if (other.miny < this.miny) {
						this.miny = other.miny;
					}
					if (other.maxy > this.maxy) {
						this.maxy = other.maxy;
					}
				}
			}
		} else if (arguments.length === 2) {
			let x = arguments[0], y = arguments[1];
			if (this.isNull()) {
				this.minx = x;
				this.maxx = x;
				this.miny = y;
				this.maxy = y;
			} else {
				if (x < this.minx) {
					this.minx = x;
				}
				if (x > this.maxx) {
					this.maxx = x;
				}
				if (y < this.miny) {
					this.miny = y;
				}
				if (y > this.maxy) {
					this.maxy = y;
				}
			}
		}
	},
	minExtent: function () {
		if (this.isNull()) return 0.0;
		var w = this.getWidth();
		var h = this.getHeight();
		if (w < h) return w;
		return h;
	},
	getWidth: function () {
		if (this.isNull()) {
			return 0;
		}
		return this.maxx - this.minx;
	},
	compareTo: function (o) {
		var env = o;
		if (this.isNull()) {
			if (env.isNull()) return 0;
			return -1;
		} else {
			if (env.isNull()) return 1;
		}
		if (this.minx < env.minx) return -1;
		if (this.minx > env.minx) return 1;
		if (this.miny < env.miny) return -1;
		if (this.miny > env.miny) return 1;
		if (this.maxx < env.maxx) return -1;
		if (this.maxx > env.maxx) return 1;
		if (this.maxy < env.maxy) return -1;
		if (this.maxy > env.maxy) return 1;
		return 0;
	},
	translate: function (transX, transY) {
		if (this.isNull()) {
			return null;
		}
		this.init(this.getMinX() + transX, this.getMaxX() + transX, this.getMinY() + transY, this.getMaxY() + transY);
	},
	toString: function () {
		return "Env[" + this.minx + " : " + this.maxx + ", " + this.miny + " : " + this.maxy + "]";
	},
	setToNull: function () {
		this.minx = 0;
		this.maxx = -1;
		this.miny = 0;
		this.maxy = -1;
	},
	getHeight: function () {
		if (this.isNull()) {
			return 0;
		}
		return this.maxy - this.miny;
	},
	maxExtent: function () {
		if (this.isNull()) return 0.0;
		var w = this.getWidth();
		var h = this.getHeight();
		if (w > h) return w;
		return h;
	},
	expandBy: function () {
		if (arguments.length === 1) {
			let distance = arguments[0];
			this.expandBy(distance, distance);
		} else if (arguments.length === 2) {
			let deltaX = arguments[0], deltaY = arguments[1];
			if (this.isNull()) return null;
			this.minx -= deltaX;
			this.maxx += deltaX;
			this.miny -= deltaY;
			this.maxy += deltaY;
			if (this.minx > this.maxx || this.miny > this.maxy) this.setToNull();
		}
	},
	contains: function () {
		if (arguments.length === 1) {
			if (arguments[0] instanceof Envelope) {
				let other = arguments[0];
				return this.covers(other);
			} else if (arguments[0] instanceof Coordinate) {
				let p = arguments[0];
				return this.covers(p);
			}
		} else if (arguments.length === 2) {
			let x = arguments[0], y = arguments[1];
			return this.covers(x, y);
		}
	},
	centre: function () {
		if (this.isNull()) return null;
		return new Coordinate((this.getMinX() + this.getMaxX()) / 2.0, (this.getMinY() + this.getMaxY()) / 2.0);
	},
	init: function () {
		if (arguments.length === 0) {
			this.setToNull();
		} else if (arguments.length === 1) {
			if (arguments[0] instanceof Coordinate) {
				let p = arguments[0];
				this.init(p.x, p.x, p.y, p.y);
			} else if (arguments[0] instanceof Envelope) {
				let env = arguments[0];
				this.minx = env.minx;
				this.maxx = env.maxx;
				this.miny = env.miny;
				this.maxy = env.maxy;
			}
		} else if (arguments.length === 2) {
			let p1 = arguments[0], p2 = arguments[1];
			this.init(p1.x, p2.x, p1.y, p2.y);
		} else if (arguments.length === 4) {
			let x1 = arguments[0], x2 = arguments[1], y1 = arguments[2], y2 = arguments[3];
			if (x1 < x2) {
				this.minx = x1;
				this.maxx = x2;
			} else {
				this.minx = x2;
				this.maxx = x1;
			}
			if (y1 < y2) {
				this.miny = y1;
				this.maxy = y2;
			} else {
				this.miny = y2;
				this.maxy = y1;
			}
		}
	},
	getMaxY: function () {
		return this.maxy;
	},
	distance: function (env) {
		if (this.intersects(env)) return 0;
		var dx = 0.0;
		if (this.maxx < env.minx) dx = env.minx - this.maxx; else if (this.minx > env.maxx) dx = this.minx - env.maxx;
		var dy = 0.0;
		if (this.maxy < env.miny) dy = env.miny - this.maxy; else if (this.miny > env.maxy) dy = this.miny - env.maxy;
		if (dx === 0.0) return dy;
		if (dy === 0.0) return dx;
		return Math.sqrt(dx * dx + dy * dy);
	},
	hashCode: function () {
		var result = 17;
		result = 37 * result + Coordinate.hashCode(this.minx);
		result = 37 * result + Coordinate.hashCode(this.maxx);
		result = 37 * result + Coordinate.hashCode(this.miny);
		result = 37 * result + Coordinate.hashCode(this.maxy);
		return result;
	},
	interfaces_: function () {
		return [Comparable, Serializable];
	},
	getClass: function () {
		return Envelope;
	}
});
Envelope.intersects = function () {
	if (arguments.length === 3) {
		let p1 = arguments[0], p2 = arguments[1], q = arguments[2];
		if (q.x >= (p1.x < p2.x ? p1.x : p2.x) && q.x <= (p1.x > p2.x ? p1.x : p2.x) && (q.y >= (p1.y < p2.y ? p1.y : p2.y) && q.y <= (p1.y > p2.y ? p1.y : p2.y))) {
			return true;
		}
		return false;
	} else if (arguments.length === 4) {
		let p1 = arguments[0], p2 = arguments[1], q1 = arguments[2], q2 = arguments[3];
		var minq = Math.min(q1.x, q2.x);
		var maxq = Math.max(q1.x, q2.x);
		var minp = Math.min(p1.x, p2.x);
		var maxp = Math.max(p1.x, p2.x);
		if (minp > maxq) return false;
		if (maxp < minq) return false;
		minq = Math.min(q1.y, q2.y);
		maxq = Math.max(q1.y, q2.y);
		minp = Math.min(p1.y, p2.y);
		maxp = Math.max(p1.y, p2.y);
		if (minp > maxq) return false;
		if (maxp < minq) return false;
		return true;
	}
};
Envelope.serialVersionUID = 5873921885273102420;

const regExes = {
  'typeStr': /^\s*(\w+)\s*\(\s*(.*)\s*\)\s*$/,
  'emptyTypeStr': /^\s*(\w+)\s*EMPTY\s*$/,
  'spaces': /\s+/,
  'parenComma': /\)\s*,\s*\(/,
  'doubleParenComma': /\)\s*\)\s*,\s*\(\s*\(/, // can't use {2} here
  'trimParens': /^\s*\(?(.*?)\)?\s*$/
};

/**
 * Class for reading and writing Well-Known Text.
 *
 * NOTE: Adapted from OpenLayers 2.11 implementation.
 */

/** Create a new parser for WKT
 *
 * @param {GeometryFactory} geometryFactory
 * @return An instance of WKTParser.
 * @constructor
 * @private
 */
function WKTParser (geometryFactory) {
  this.geometryFactory = geometryFactory || new GeometryFactory();
}

extend$1(WKTParser.prototype, {
  /**
   * Deserialize a WKT string and return a geometry. Supports WKT for POINT,
   * MULTIPOINT, LINESTRING, LINEARRING, MULTILINESTRING, POLYGON, MULTIPOLYGON,
   * and GEOMETRYCOLLECTION.
   *
   * @param {String} wkt A WKT string.
   * @return {Geometry} A geometry instance.
   * @private
   */
  read (wkt) {
    var geometry, type, str;
    wkt = wkt.replace(/[\n\r]/g, ' ');
    var matches = regExes.typeStr.exec(wkt);
    if (wkt.search('EMPTY') !== -1) {
      matches = regExes.emptyTypeStr.exec(wkt);
      matches[2] = undefined;
    }
    if (matches) {
      type = matches[1].toLowerCase();
      str = matches[2];
      if (parse[type]) {
        geometry = parse[type].apply(this, [str]);
      }
    }

    if (geometry === undefined) throw new Error('Could not parse WKT ' + wkt)

    return geometry
  },

  /**
   * Serialize a geometry into a WKT string.
   *
   * @param {Geometry} geometry A feature or array of features.
   * @return {String} The WKT string representation of the input geometries.
   * @private
   */
  write (geometry) {
    return this.extractGeometry(geometry)
  },

  /**
   * Entry point to construct the WKT for a single Geometry object.
   *
   * @param {Geometry} geometry
   * @return {String} A WKT string of representing the geometry.
   * @private
   */
  extractGeometry (geometry) {
    var type = geometry.getGeometryType().toLowerCase();
    if (!extract[type]) {
      return null
    }
    var wktType = type.toUpperCase();
    var data;
    if (geometry.isEmpty()) {
      data = wktType + ' EMPTY';
    } else {
      data = wktType + '(' + extract[type].apply(this, [geometry]) + ')';
    }
    return data
  }
});

/**
 * Object with properties corresponding to the geometry types. Property values
 * are functions that do the actual data extraction.
 * @private
 */
const extract = {
  coordinate (coordinate) {
    return coordinate.x + ' ' + coordinate.y
  },

  /**
   * Return a space delimited string of point coordinates.
   *
   * @param {Point}
   *          point
   * @return {String} A string of coordinates representing the point.
   */
  point (point) {
    return extract.coordinate.call(this, point.coordinates.coordinates[0])
  },

  /**
   * Return a comma delimited string of point coordinates from a multipoint.
   *
   * @param {MultiPoint}
   *          multipoint
   * @return {String} A string of point coordinate strings representing the
   *         multipoint.
   */
  multipoint (multipoint) {
    var array = [];
    for (let i = 0, len = multipoint.geometries.length; i < len; ++i) {
      array.push('(' + extract.point.apply(this, [multipoint.geometries[i]]) + ')');
    }
    return array.join(',')
  },

  /**
   * Return a comma delimited string of point coordinates from a line.
   *
   * @param {LineString} linestring
   * @return {String} A string of point coordinate strings representing the linestring.
   */
  linestring (linestring) {
    var array = [];
    for (let i = 0, len = linestring.points.coordinates.length; i < len; ++i) {
      array.push(extract.coordinate.apply(this, [linestring.points.coordinates[i]]));
    }
    return array.join(',')
  },

  linearring (linearring) {
    var array = [];
    for (let i = 0, len = linearring.points.coordinates.length; i < len; ++i) {
      array.push(extract.coordinate.apply(this, [linearring.points.coordinates[i]]));
    }
    return array.join(',')
  },

  /**
   * Return a comma delimited string of linestring strings from a
   * multilinestring.
   *
   * @param {MultiLineString} multilinestring
   * @return {String} A string of of linestring strings representing the multilinestring.
   */
  multilinestring (multilinestring) {
    var array = [];
    for (let i = 0, len = multilinestring.geometries.length; i < len; ++i) {
      array.push('(' +
        extract.linestring.apply(this, [multilinestring.geometries[i]]) +
        ')');
    }
    return array.join(',')
  },

  /**
   * Return a comma delimited string of linear ring arrays from a polygon.
   *
   * @param {Polygon} polygon
   * @return {String} An array of linear ring arrays representing the polygon.
   */
  polygon (polygon) {
    var array = [];
    array.push('(' + extract.linestring.apply(this, [polygon.shell]) + ')');
    for (let i = 0, len = polygon.holes.length; i < len; ++i) {
      array.push('(' + extract.linestring.apply(this, [polygon.holes[i]]) + ')');
    }
    return array.join(',')
  },

  /**
   * Return an array of polygon arrays from a multipolygon.
   *
   * @param {MultiPolygon} multipolygon
   * @return {String} An array of polygon arrays representing the multipolygon.
   */
  multipolygon (multipolygon) {
    var array = [];
    for (let i = 0, len = multipolygon.geometries.length; i < len; ++i) {
      array.push('(' + extract.polygon.apply(this, [multipolygon.geometries[i]]) + ')');
    }
    return array.join(',')
  },

  /**
   * Return the WKT portion between 'GEOMETRYCOLLECTION(' and ')' for an
   * geometrycollection.
   *
   * @param {GeometryCollection} collection
   * @return {String} internal WKT representation of the collection.
   */
  geometrycollection (collection) {
    var array = [];
    for (let i = 0, len = collection.geometries.length; i < len; ++i) {
      array.push(this.extractGeometry(collection.geometries[i]));
    }
    return array.join(',')
  }
};

/**
 * Object with properties corresponding to the geometry types. Property values
 * are functions that do the actual parsing.
 * @private
 */
const parse = {
  /**
   * Return point geometry given a point WKT fragment.
   *
   * @param {String} str A WKT fragment representing the point.
   * @return {Point} A point geometry.
   * @private
   */
  point (str) {
    if (str === undefined) {
      return this.geometryFactory.createPoint()
    }

    var coords = str.trim().split(regExes.spaces);
    return this.geometryFactory.createPoint(new Coordinate(Number.parseFloat(coords[0]),
      Number.parseFloat(coords[1])))
  },

  /**
   * Return a multipoint geometry given a multipoint WKT fragment.
   *
   * @param {String} str A WKT fragment representing the multipoint.
   * @return {Point} A multipoint feature.
   * @private
   */
  multipoint (str) {
    if (str === undefined) {
      return this.geometryFactory.createMultiPoint()
    }

    var point;
    var points = str.trim().split(',');
    var components = [];
    for (let i = 0, len = points.length; i < len; ++i) {
      point = points[i].replace(regExes.trimParens, '$1');
      components.push(parse.point.apply(this, [point]));
    }
    return this.geometryFactory.createMultiPoint(components)
  },

  /**
   * Return a linestring geometry given a linestring WKT fragment.
   *
   * @param {String} str A WKT fragment representing the linestring.
   * @return {LineString} A linestring geometry.
   * @private
   */
  linestring (str) {
    if (str === undefined) {
      return this.geometryFactory.createLineString()
    }

    var points = str.trim().split(',');
    var components = [];
    var coords;
    for (let i = 0, len = points.length; i < len; ++i) {
      coords = points[i].trim().split(regExes.spaces);
      components.push(new Coordinate(Number.parseFloat(coords[0]), Number.parseFloat(coords[1])));
    }
    return this.geometryFactory.createLineString(components)
  },

  /**
   * Return a linearring geometry given a linearring WKT fragment.
   *
   * @param {String} str A WKT fragment representing the linearring.
   * @return {LinearRing} A linearring geometry.
   * @private
   */
  linearring (str) {
    if (str === undefined) {
      return this.geometryFactory.createLinearRing()
    }

    var points = str.trim().split(',');
    var components = [];
    var coords;
    for (let i = 0, len = points.length; i < len; ++i) {
      coords = points[i].trim().split(regExes.spaces);
      components.push(new Coordinate(Number.parseFloat(coords[0]), Number.parseFloat(coords[1])));
    }
    return this.geometryFactory.createLinearRing(components)
  },

  /**
   * Return a multilinestring geometry given a multilinestring WKT fragment.
   *
   * @param {String} str A WKT fragment representing the multilinestring.
   * @return {MultiLineString} A multilinestring geometry.
   * @private
   */
  multilinestring (str) {
    if (str === undefined) {
      return this.geometryFactory.createMultiLineString()
    }

    var line;
    var lines = str.trim().split(regExes.parenComma);
    var components = [];
    for (let i = 0, len = lines.length; i < len; ++i) {
      line = lines[i].replace(regExes.trimParens, '$1');
      components.push(parse.linestring.apply(this, [line]));
    }
    return this.geometryFactory.createMultiLineString(components)
  },

  /**
   * Return a polygon geometry given a polygon WKT fragment.
   *
   * @param {String} str A WKT fragment representing the polygon.
   * @return {Polygon} A polygon geometry.
   * @private
   */
  polygon (str) {
    if (str === undefined) {
      return this.geometryFactory.createPolygon()
    }

    var ring, linestring, linearring;
    var rings = str.trim().split(regExes.parenComma);
    var shell;
    var holes = [];
    for (let i = 0, len = rings.length; i < len; ++i) {
      ring = rings[i].replace(regExes.trimParens, '$1');
      linestring = parse.linestring.apply(this, [ring]);
      linearring = this.geometryFactory.createLinearRing(linestring.points);
      if (i === 0) {
        shell = linearring;
      } else {
        holes.push(linearring);
      }
    }
    return this.geometryFactory.createPolygon(shell, holes)
  },

  /**
   * Return a multipolygon geometry given a multipolygon WKT fragment.
   *
   * @param {String} str A WKT fragment representing the multipolygon.
   * @return {MultiPolygon} A multipolygon geometry.
   * @private
   */
  multipolygon (str) {
    if (str === undefined) {
      return this.geometryFactory.createMultiPolygon()
    }

    var polygon;
    var polygons = str.trim().split(regExes.doubleParenComma);
    var components = [];
    for (let i = 0, len = polygons.length; i < len; ++i) {
      polygon = polygons[i].replace(regExes.trimParens, '$1');
      components.push(parse.polygon.apply(this, [polygon]));
    }
    return this.geometryFactory.createMultiPolygon(components)
  },

  /**
   * Return a geometrycollection given a geometrycollection WKT fragment.
   *
   * @param {String} str A WKT fragment representing the geometrycollection.
   * @return {GeometryCollection}
   * @private
   */
  geometrycollection (str) {
    if (str === undefined) {
      return this.geometryFactory.createGeometryCollection()
    }

    // separate components of the collection with |
    str = str.replace(/,\s*([A-Za-z])/g, '|$1');
    var wktArray = str.trim().split('|');
    var components = [];
    for (let i = 0, len = wktArray.length; i < len; ++i) {
      components.push(this.read(wktArray[i]));
    }
    return this.geometryFactory.createGeometryCollection(components)
  }
};

/**
 * Writes the Well-Known Text representation of a {@link Geometry}. The
 * Well-Known Text format is defined in the <A
 * HREF="http://www.opengis.org/techno/specs.htm"> OGC Simple Features
 * Specification for SQL</A>.
 * <p>
 * The <code>WKTWriter</code> outputs coordinates rounded to the precision
 * model. Only the maximum number of decimal places necessary to represent the
 * ordinates to the required precision will be output.
 * <p>
 * The SFS WKT spec does not define a special tag for {@link LinearRing}s.
 * Under the spec, rings are output as <code>LINESTRING</code>s.
 */

/**
 * @param {GeometryFactory} geometryFactory
 * @constructor
 */
function WKTWriter (geometryFactory) {
  this.parser = new WKTParser(geometryFactory);
}

extend$1(WKTWriter.prototype, {
  /**
   * Converts a <code>Geometry</code> to its Well-known Text representation.
   *
   * @param {Geometry} geometry a <code>Geometry</code> to process.
   * @return {string} a <Geometry Tagged Text> string (see the OpenGIS Simple
   *         Features Specification).
   * @memberof WKTWriter
   */
  write (geometry) {
    return this.parser.write(geometry)
  }
});

extend$1(WKTWriter, {
  /**
   * Generates the WKT for a <tt>LINESTRING</tt> specified by two
   * {@link Coordinate}s.
   *
   * @param p0 the first coordinate.
   * @param p1 the second coordinate.
   *
   * @return the WKT.
   * @private
   */
  toLineString (p0, p1) {
    if (arguments.length !== 2) {
      throw new Error('Not implemented')
    }

    return 'LINESTRING ( ' + p0.x + ' ' + p0.y + ', ' + p1.x + ' ' + p1.y + ' )'
  }
});

function LineIntersector() {
	this.result = null;
	this.inputLines = Array(2).fill().map(() => Array(2));
	this.intPt = new Array(2).fill(null);
	this.intLineIndex = null;
	this._isProper = null;
	this.pa = null;
	this.pb = null;
	this.precisionModel = null;
	this.intPt[0] = new Coordinate();
	this.intPt[1] = new Coordinate();
	this.pa = this.intPt[0];
	this.pb = this.intPt[1];
	this.result = 0;
}
extend$1(LineIntersector.prototype, {
	getIndexAlongSegment: function (segmentIndex, intIndex) {
		this.computeIntLineIndex();
		return this.intLineIndex[segmentIndex][intIndex];
	},
	getTopologySummary: function () {
		var catBuf = new StringBuffer();
		if (this.isEndPoint()) catBuf.append(" endpoint");
		if (this._isProper) catBuf.append(" proper");
		if (this.isCollinear()) catBuf.append(" collinear");
		return catBuf.toString();
	},
	computeIntersection: function (p1, p2, p3, p4) {
		this.inputLines[0][0] = p1;
		this.inputLines[0][1] = p2;
		this.inputLines[1][0] = p3;
		this.inputLines[1][1] = p4;
		this.result = this.computeIntersect(p1, p2, p3, p4);
	},
	getIntersectionNum: function () {
		return this.result;
	},
	computeIntLineIndex: function () {
		if (arguments.length === 0) {
			if (this.intLineIndex === null) {
				this.intLineIndex = Array(2).fill().map(() => Array(2));
				this.computeIntLineIndex(0);
				this.computeIntLineIndex(1);
			}
		} else if (arguments.length === 1) {
			let segmentIndex = arguments[0];
			var dist0 = this.getEdgeDistance(segmentIndex, 0);
			var dist1 = this.getEdgeDistance(segmentIndex, 1);
			if (dist0 > dist1) {
				this.intLineIndex[segmentIndex][0] = 0;
				this.intLineIndex[segmentIndex][1] = 1;
			} else {
				this.intLineIndex[segmentIndex][0] = 1;
				this.intLineIndex[segmentIndex][1] = 0;
			}
		}
	},
	isProper: function () {
		return this.hasIntersection() && this._isProper;
	},
	setPrecisionModel: function (precisionModel) {
		this.precisionModel = precisionModel;
	},
	isInteriorIntersection: function () {
		if (arguments.length === 0) {
			if (this.isInteriorIntersection(0)) return true;
			if (this.isInteriorIntersection(1)) return true;
			return false;
		} else if (arguments.length === 1) {
			let inputLineIndex = arguments[0];
			for (var i = 0; i < this.result; i++) {
				if (!(this.intPt[i].equals2D(this.inputLines[inputLineIndex][0]) || this.intPt[i].equals2D(this.inputLines[inputLineIndex][1]))) {
					return true;
				}
			}
			return false;
		}
	},
	getIntersection: function (intIndex) {
		return this.intPt[intIndex];
	},
	isEndPoint: function () {
		return this.hasIntersection() && !this._isProper;
	},
	hasIntersection: function () {
		return this.result !== LineIntersector.NO_INTERSECTION;
	},
	getEdgeDistance: function (segmentIndex, intIndex) {
		var dist = LineIntersector.computeEdgeDistance(this.intPt[intIndex], this.inputLines[segmentIndex][0], this.inputLines[segmentIndex][1]);
		return dist;
	},
	isCollinear: function () {
		return this.result === LineIntersector.COLLINEAR_INTERSECTION;
	},
	toString: function () {
		return WKTWriter.toLineString(this.inputLines[0][0], this.inputLines[0][1]) + " - " + WKTWriter.toLineString(this.inputLines[1][0], this.inputLines[1][1]) + this.getTopologySummary();
	},
	getEndpoint: function (segmentIndex, ptIndex) {
		return this.inputLines[segmentIndex][ptIndex];
	},
	isIntersection: function (pt) {
		for (var i = 0; i < this.result; i++) {
			if (this.intPt[i].equals2D(pt)) {
				return true;
			}
		}
		return false;
	},
	getIntersectionAlongSegment: function (segmentIndex, intIndex) {
		this.computeIntLineIndex();
		return this.intPt[this.intLineIndex[segmentIndex][intIndex]];
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return LineIntersector;
	}
});
LineIntersector.computeEdgeDistance = function (p, p0, p1) {
	var dx = Math.abs(p1.x - p0.x);
	var dy = Math.abs(p1.y - p0.y);
	var dist = -1.0;
	if (p.equals(p0)) {
		dist = 0.0;
	} else if (p.equals(p1)) {
		if (dx > dy) dist = dx; else dist = dy;
	} else {
		var pdx = Math.abs(p.x - p0.x);
		var pdy = Math.abs(p.y - p0.y);
		if (dx > dy) dist = pdx; else dist = pdy;
		if (dist === 0.0 && !p.equals(p0)) {
			dist = Math.max(pdx, pdy);
		}
	}
	Assert.isTrue(!(dist === 0.0 && !p.equals(p0)), "Bad distance calculation");
	return dist;
};
LineIntersector.nonRobustComputeEdgeDistance = function (p, p1, p2) {
	var dx = p.x - p1.x;
	var dy = p.y - p1.y;
	var dist = Math.sqrt(dx * dx + dy * dy);
	Assert.isTrue(!(dist === 0.0 && !p.equals(p1)), "Invalid distance calculation");
	return dist;
};
LineIntersector.DONT_INTERSECT = 0;
LineIntersector.DO_INTERSECT = 1;
LineIntersector.COLLINEAR = 2;
LineIntersector.NO_INTERSECTION = 0;
LineIntersector.POINT_INTERSECTION = 1;
LineIntersector.COLLINEAR_INTERSECTION = 2;

function RobustLineIntersector() {
	LineIntersector.apply(this);
}
inherits(RobustLineIntersector, LineIntersector);
extend$1(RobustLineIntersector.prototype, {
	isInSegmentEnvelopes: function (intPt) {
		var env0 = new Envelope(this.inputLines[0][0], this.inputLines[0][1]);
		var env1 = new Envelope(this.inputLines[1][0], this.inputLines[1][1]);
		return env0.contains(intPt) && env1.contains(intPt);
	},
	computeIntersection: function () {
		if (arguments.length === 3) {
			let p = arguments[0], p1 = arguments[1], p2 = arguments[2];
			this._isProper = false;
			if (Envelope.intersects(p1, p2, p)) {
				if (CGAlgorithms.orientationIndex(p1, p2, p) === 0 && CGAlgorithms.orientationIndex(p2, p1, p) === 0) {
					this._isProper = true;
					if (p.equals(p1) || p.equals(p2)) {
						this._isProper = false;
					}
					this.result = LineIntersector.POINT_INTERSECTION;
					return null;
				}
			}
			this.result = LineIntersector.NO_INTERSECTION;
		} else return LineIntersector.prototype.computeIntersection.apply(this, arguments);
	},
	normalizeToMinimum: function (n1, n2, n3, n4, normPt) {
		normPt.x = this.smallestInAbsValue(n1.x, n2.x, n3.x, n4.x);
		normPt.y = this.smallestInAbsValue(n1.y, n2.y, n3.y, n4.y);
		n1.x -= normPt.x;
		n1.y -= normPt.y;
		n2.x -= normPt.x;
		n2.y -= normPt.y;
		n3.x -= normPt.x;
		n3.y -= normPt.y;
		n4.x -= normPt.x;
		n4.y -= normPt.y;
	},
	safeHCoordinateIntersection: function (p1, p2, q1, q2) {
		var intPt = null;
		try {
			intPt = HCoordinate.intersection(p1, p2, q1, q2);
		} catch (e) {
			if (e instanceof NotRepresentableException) {
				intPt = RobustLineIntersector.nearestEndpoint(p1, p2, q1, q2);
			} else throw e;
		} finally {}
		return intPt;
	},
	intersection: function (p1, p2, q1, q2) {
		var intPt = this.intersectionWithNormalization(p1, p2, q1, q2);
		if (!this.isInSegmentEnvelopes(intPt)) {
			intPt = new Coordinate(RobustLineIntersector.nearestEndpoint(p1, p2, q1, q2));
		}
		if (this.precisionModel !== null) {
			this.precisionModel.makePrecise(intPt);
		}
		return intPt;
	},
	smallestInAbsValue: function (x1, x2, x3, x4) {
		var x = x1;
		var xabs = Math.abs(x);
		if (Math.abs(x2) < xabs) {
			x = x2;
			xabs = Math.abs(x2);
		}
		if (Math.abs(x3) < xabs) {
			x = x3;
			xabs = Math.abs(x3);
		}
		if (Math.abs(x4) < xabs) {
			x = x4;
		}
		return x;
	},
	checkDD: function (p1, p2, q1, q2, intPt) {
		var intPtDD = CGAlgorithmsDD.intersection(p1, p2, q1, q2);
		var isIn = this.isInSegmentEnvelopes(intPtDD);
		System.out.println("DD in env = " + isIn + "  --------------------- " + intPtDD);
		if (intPt.distance(intPtDD) > 0.0001) {
			System.out.println("Distance = " + intPt.distance(intPtDD));
		}
	},
	intersectionWithNormalization: function (p1, p2, q1, q2) {
		var n1 = new Coordinate(p1);
		var n2 = new Coordinate(p2);
		var n3 = new Coordinate(q1);
		var n4 = new Coordinate(q2);
		var normPt = new Coordinate();
		this.normalizeToEnvCentre(n1, n2, n3, n4, normPt);
		var intPt = this.safeHCoordinateIntersection(n1, n2, n3, n4);
		intPt.x += normPt.x;
		intPt.y += normPt.y;
		return intPt;
	},
	computeCollinearIntersection: function (p1, p2, q1, q2) {
		var p1q1p2 = Envelope.intersects(p1, p2, q1);
		var p1q2p2 = Envelope.intersects(p1, p2, q2);
		var q1p1q2 = Envelope.intersects(q1, q2, p1);
		var q1p2q2 = Envelope.intersects(q1, q2, p2);
		if (p1q1p2 && p1q2p2) {
			this.intPt[0] = q1;
			this.intPt[1] = q2;
			return LineIntersector.COLLINEAR_INTERSECTION;
		}
		if (q1p1q2 && q1p2q2) {
			this.intPt[0] = p1;
			this.intPt[1] = p2;
			return LineIntersector.COLLINEAR_INTERSECTION;
		}
		if (p1q1p2 && q1p1q2) {
			this.intPt[0] = q1;
			this.intPt[1] = p1;
			return q1.equals(p1) && !p1q2p2 && !q1p2q2 ? LineIntersector.POINT_INTERSECTION : LineIntersector.COLLINEAR_INTERSECTION;
		}
		if (p1q1p2 && q1p2q2) {
			this.intPt[0] = q1;
			this.intPt[1] = p2;
			return q1.equals(p2) && !p1q2p2 && !q1p1q2 ? LineIntersector.POINT_INTERSECTION : LineIntersector.COLLINEAR_INTERSECTION;
		}
		if (p1q2p2 && q1p1q2) {
			this.intPt[0] = q2;
			this.intPt[1] = p1;
			return q2.equals(p1) && !p1q1p2 && !q1p2q2 ? LineIntersector.POINT_INTERSECTION : LineIntersector.COLLINEAR_INTERSECTION;
		}
		if (p1q2p2 && q1p2q2) {
			this.intPt[0] = q2;
			this.intPt[1] = p2;
			return q2.equals(p2) && !p1q1p2 && !q1p1q2 ? LineIntersector.POINT_INTERSECTION : LineIntersector.COLLINEAR_INTERSECTION;
		}
		return LineIntersector.NO_INTERSECTION;
	},
	normalizeToEnvCentre: function (n00, n01, n10, n11, normPt) {
		var minX0 = n00.x < n01.x ? n00.x : n01.x;
		var minY0 = n00.y < n01.y ? n00.y : n01.y;
		var maxX0 = n00.x > n01.x ? n00.x : n01.x;
		var maxY0 = n00.y > n01.y ? n00.y : n01.y;
		var minX1 = n10.x < n11.x ? n10.x : n11.x;
		var minY1 = n10.y < n11.y ? n10.y : n11.y;
		var maxX1 = n10.x > n11.x ? n10.x : n11.x;
		var maxY1 = n10.y > n11.y ? n10.y : n11.y;
		var intMinX = minX0 > minX1 ? minX0 : minX1;
		var intMaxX = maxX0 < maxX1 ? maxX0 : maxX1;
		var intMinY = minY0 > minY1 ? minY0 : minY1;
		var intMaxY = maxY0 < maxY1 ? maxY0 : maxY1;
		var intMidX = (intMinX + intMaxX) / 2.0;
		var intMidY = (intMinY + intMaxY) / 2.0;
		normPt.x = intMidX;
		normPt.y = intMidY;
		n00.x -= normPt.x;
		n00.y -= normPt.y;
		n01.x -= normPt.x;
		n01.y -= normPt.y;
		n10.x -= normPt.x;
		n10.y -= normPt.y;
		n11.x -= normPt.x;
		n11.y -= normPt.y;
	},
	computeIntersect: function (p1, p2, q1, q2) {
		this._isProper = false;
		if (!Envelope.intersects(p1, p2, q1, q2)) return LineIntersector.NO_INTERSECTION;
		var Pq1 = CGAlgorithms.orientationIndex(p1, p2, q1);
		var Pq2 = CGAlgorithms.orientationIndex(p1, p2, q2);
		if (Pq1 > 0 && Pq2 > 0 || Pq1 < 0 && Pq2 < 0) {
			return LineIntersector.NO_INTERSECTION;
		}
		var Qp1 = CGAlgorithms.orientationIndex(q1, q2, p1);
		var Qp2 = CGAlgorithms.orientationIndex(q1, q2, p2);
		if (Qp1 > 0 && Qp2 > 0 || Qp1 < 0 && Qp2 < 0) {
			return LineIntersector.NO_INTERSECTION;
		}
		var collinear = Pq1 === 0 && Pq2 === 0 && Qp1 === 0 && Qp2 === 0;
		if (collinear) {
			return this.computeCollinearIntersection(p1, p2, q1, q2);
		}
		if (Pq1 === 0 || Pq2 === 0 || Qp1 === 0 || Qp2 === 0) {
			this._isProper = false;
			if (p1.equals2D(q1) || p1.equals2D(q2)) {
				this.intPt[0] = p1;
			} else if (p2.equals2D(q1) || p2.equals2D(q2)) {
				this.intPt[0] = p2;
			} else if (Pq1 === 0) {
				this.intPt[0] = new Coordinate(q1);
			} else if (Pq2 === 0) {
				this.intPt[0] = new Coordinate(q2);
			} else if (Qp1 === 0) {
				this.intPt[0] = new Coordinate(p1);
			} else if (Qp2 === 0) {
				this.intPt[0] = new Coordinate(p2);
			}
		} else {
			this._isProper = true;
			this.intPt[0] = this.intersection(p1, p2, q1, q2);
		}
		return LineIntersector.POINT_INTERSECTION;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return RobustLineIntersector;
	}
});
RobustLineIntersector.nearestEndpoint = function (p1, p2, q1, q2) {
	var nearestPt = p1;
	var minDist = CGAlgorithms.distancePointLine(p1, q1, q2);
	var dist = CGAlgorithms.distancePointLine(p2, q1, q2);
	if (dist < minDist) {
		minDist = dist;
		nearestPt = p2;
	}
	dist = CGAlgorithms.distancePointLine(q1, p1, p2);
	if (dist < minDist) {
		minDist = dist;
		nearestPt = q1;
	}
	dist = CGAlgorithms.distancePointLine(q2, p1, p2);
	if (dist < minDist) {
		minDist = dist;
		nearestPt = q2;
	}
	return nearestPt;
};

function RobustDeterminant() {}
extend$1(RobustDeterminant.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return RobustDeterminant;
	}
});
RobustDeterminant.orientationIndex = function (p1, p2, q) {
	var dx1 = p2.x - p1.x;
	var dy1 = p2.y - p1.y;
	var dx2 = q.x - p2.x;
	var dy2 = q.y - p2.y;
	return RobustDeterminant.signOfDet2x2(dx1, dy1, dx2, dy2);
};
RobustDeterminant.signOfDet2x2 = function (x1, y1, x2, y2) {
	var sign = null;
	var swap = null;
	var k = null;
	sign = 1;
	if (x1 === 0.0 || y2 === 0.0) {
		if (y1 === 0.0 || x2 === 0.0) {
			return 0;
		} else if (y1 > 0) {
			if (x2 > 0) {
				return -sign;
			} else {
				return sign;
			}
		} else {
			if (x2 > 0) {
				return sign;
			} else {
				return -sign;
			}
		}
	}
	if (y1 === 0.0 || x2 === 0.0) {
		if (y2 > 0) {
			if (x1 > 0) {
				return sign;
			} else {
				return -sign;
			}
		} else {
			if (x1 > 0) {
				return -sign;
			} else {
				return sign;
			}
		}
	}
	if (0.0 < y1) {
		if (0.0 < y2) {
			if (y1 <= y2) {

			} else {
				sign = -sign;
				swap = x1;
				x1 = x2;
				x2 = swap;
				swap = y1;
				y1 = y2;
				y2 = swap;
			}
		} else {
			if (y1 <= -y2) {
				sign = -sign;
				x2 = -x2;
				y2 = -y2;
			} else {
				swap = x1;
				x1 = -x2;
				x2 = swap;
				swap = y1;
				y1 = -y2;
				y2 = swap;
			}
		}
	} else {
		if (0.0 < y2) {
			if (-y1 <= y2) {
				sign = -sign;
				x1 = -x1;
				y1 = -y1;
			} else {
				swap = -x1;
				x1 = x2;
				x2 = swap;
				swap = -y1;
				y1 = y2;
				y2 = swap;
			}
		} else {
			if (y1 >= y2) {
				x1 = -x1;
				y1 = -y1;
				x2 = -x2;
				y2 = -y2;

			} else {
				sign = -sign;
				swap = -x1;
				x1 = -x2;
				x2 = swap;
				swap = -y1;
				y1 = -y2;
				y2 = swap;
			}
		}
	}
	if (0.0 < x1) {
		if (0.0 < x2) {
			if (x1 <= x2) {

			} else {
				return sign;
			}
		} else {
			return sign;
		}
	} else {
		if (0.0 < x2) {
			return -sign;
		} else {
			if (x1 >= x2) {
				sign = -sign;
				x1 = -x1;
				x2 = -x2;

			} else {
				return -sign;
			}
		}
	}
	while (true) {
		k = Math.floor(x2 / x1);
		x2 = x2 - k * x1;
		y2 = y2 - k * y1;
		if (y2 < 0.0) {
			return -sign;
		}
		if (y2 > y1) {
			return sign;
		}
		if (x1 > x2 + x2) {
			if (y1 < y2 + y2) {
				return sign;
			}
		} else {
			if (y1 > y2 + y2) {
				return -sign;
			} else {
				x2 = x1 - x2;
				y2 = y1 - y2;
				sign = -sign;
			}
		}
		if (y2 === 0.0) {
			if (x2 === 0.0) {
				return 0;
			} else {
				return -sign;
			}
		}
		if (x2 === 0.0) {
			return sign;
		}
		k = Math.floor(x1 / x2);
		x1 = x1 - k * x2;
		y1 = y1 - k * y2;
		if (y1 < 0.0) {
			return sign;
		}
		if (y1 > y2) {
			return -sign;
		}
		if (x2 > x1 + x1) {
			if (y2 < y1 + y1) {
				return -sign;
			}
		} else {
			if (y2 > y1 + y1) {
				return sign;
			} else {
				x1 = x2 - x1;
				y1 = y2 - y1;
				sign = -sign;
			}
		}
		if (y1 === 0.0) {
			if (x1 === 0.0) {
				return 0;
			} else {
				return sign;
			}
		}
		if (x1 === 0.0) {
			return -sign;
		}
	}
};

function RayCrossingCounter() {
	this.p = null;
	this.crossingCount = 0;
	this.isPointOnSegment = false;
	let p = arguments[0];
	this.p = p;
}
extend$1(RayCrossingCounter.prototype, {
	countSegment: function (p1, p2) {
		if (p1.x < this.p.x && p2.x < this.p.x) return null;
		if (this.p.x === p2.x && this.p.y === p2.y) {
			this.isPointOnSegment = true;
			return null;
		}
		if (p1.y === this.p.y && p2.y === this.p.y) {
			var minx = p1.x;
			var maxx = p2.x;
			if (minx > maxx) {
				minx = p2.x;
				maxx = p1.x;
			}
			if (this.p.x >= minx && this.p.x <= maxx) {
				this.isPointOnSegment = true;
			}
			return null;
		}
		if (p1.y > this.p.y && p2.y <= this.p.y || p2.y > this.p.y && p1.y <= this.p.y) {
			var x1 = p1.x - this.p.x;
			var y1 = p1.y - this.p.y;
			var x2 = p2.x - this.p.x;
			var y2 = p2.y - this.p.y;
			var xIntSign = RobustDeterminant.signOfDet2x2(x1, y1, x2, y2);
			if (xIntSign === 0.0) {
				this.isPointOnSegment = true;
				return null;
			}
			if (y2 < y1) xIntSign = -xIntSign;
			if (xIntSign > 0.0) {
				this.crossingCount++;
			}
		}
	},
	isPointInPolygon: function () {
		return this.getLocation() !== Location.EXTERIOR;
	},
	getLocation: function () {
		if (this.isPointOnSegment) return Location.BOUNDARY;
		if (this.crossingCount % 2 === 1) {
			return Location.INTERIOR;
		}
		return Location.EXTERIOR;
	},
	isOnSegment: function () {
		return this.isPointOnSegment;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return RayCrossingCounter;
	}
});
RayCrossingCounter.locatePointInRing = function () {
	if (arguments[0] instanceof Coordinate && hasInterface(arguments[1], CoordinateSequence)) {
		let p = arguments[0], ring = arguments[1];
		var counter = new RayCrossingCounter(p);
		var p1 = new Coordinate();
		var p2 = new Coordinate();
		for (var i = 1; i < ring.size(); i++) {
			ring.getCoordinate(i, p1);
			ring.getCoordinate(i - 1, p2);
			counter.countSegment(p1, p2);
			if (counter.isOnSegment()) return counter.getLocation();
		}
		return counter.getLocation();
	} else if (arguments[0] instanceof Coordinate && arguments[1] instanceof Array) {
		let p = arguments[0], ring = arguments[1];
		var counter = new RayCrossingCounter(p);
		for (var i = 1; i < ring.length; i++) {
			var p1 = ring[i];
			var p2 = ring[i - 1];
			counter.countSegment(p1, p2);
			if (counter.isOnSegment()) return counter.getLocation();
		}
		return counter.getLocation();
	}
};

function CGAlgorithms() {}
extend$1(CGAlgorithms.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return CGAlgorithms;
	}
});
CGAlgorithms.orientationIndex = function (p1, p2, q) {
	return CGAlgorithmsDD.orientationIndex(p1, p2, q);
};
CGAlgorithms.signedArea = function () {
	if (arguments[0] instanceof Array) {
		let ring = arguments[0];
		if (ring.length < 3) return 0.0;
		var sum = 0.0;
		var x0 = ring[0].x;
		for (var i = 1; i < ring.length - 1; i++) {
			var x = ring[i].x - x0;
			var y1 = ring[i + 1].y;
			var y2 = ring[i - 1].y;
			sum += x * (y2 - y1);
		}
		return sum / 2.0;
	} else if (hasInterface(arguments[0], CoordinateSequence)) {
		let ring = arguments[0];
		var n = ring.size();
		if (n < 3) return 0.0;
		var p0 = new Coordinate();
		var p1 = new Coordinate();
		var p2 = new Coordinate();
		ring.getCoordinate(0, p1);
		ring.getCoordinate(1, p2);
		var x0 = p1.x;
		p2.x -= x0;
		var sum = 0.0;
		for (var i = 1; i < n - 1; i++) {
			p0.y = p1.y;
			p1.x = p2.x;
			p1.y = p2.y;
			ring.getCoordinate(i + 1, p2);
			p2.x -= x0;
			sum += p1.x * (p0.y - p2.y);
		}
		return sum / 2.0;
	}
};
CGAlgorithms.distanceLineLine = function (A, B, C, D) {
	if (A.equals(B)) return CGAlgorithms.distancePointLine(A, C, D);
	if (C.equals(D)) return CGAlgorithms.distancePointLine(D, A, B);
	var noIntersection = false;
	if (!Envelope.intersects(A, B, C, D)) {
		noIntersection = true;
	} else {
		var denom = (B.x - A.x) * (D.y - C.y) - (B.y - A.y) * (D.x - C.x);
		if (denom === 0) {
			noIntersection = true;
		} else {
			var r_num = (A.y - C.y) * (D.x - C.x) - (A.x - C.x) * (D.y - C.y);
			var s_num = (A.y - C.y) * (B.x - A.x) - (A.x - C.x) * (B.y - A.y);
			var s = s_num / denom;
			var r = r_num / denom;
			if (r < 0 || r > 1 || s < 0 || s > 1) {
				noIntersection = true;
			}
		}
	}
	if (noIntersection) {
		return MathUtil.min(CGAlgorithms.distancePointLine(A, C, D), CGAlgorithms.distancePointLine(B, C, D), CGAlgorithms.distancePointLine(C, A, B), CGAlgorithms.distancePointLine(D, A, B));
	}
	return 0.0;
};
CGAlgorithms.isPointInRing = function (p, ring) {
	return CGAlgorithms.locatePointInRing(p, ring) !== Location.EXTERIOR;
};
CGAlgorithms.computeLength = function (pts) {
	var n = pts.size();
	if (n <= 1) return 0.0;
	var len = 0.0;
	var p = new Coordinate();
	pts.getCoordinate(0, p);
	var x0 = p.x;
	var y0 = p.y;
	for (var i = 1; i < n; i++) {
		pts.getCoordinate(i, p);
		var x1 = p.x;
		var y1 = p.y;
		var dx = x1 - x0;
		var dy = y1 - y0;
		len += Math.sqrt(dx * dx + dy * dy);
		x0 = x1;
		y0 = y1;
	}
	return len;
};
CGAlgorithms.isCCW = function (ring) {
	var nPts = ring.length - 1;
	if (nPts < 3) throw new IllegalArgumentException("Ring has fewer than 4 points, so orientation cannot be determined");
	var hiPt = ring[0];
	var hiIndex = 0;
	for (var i = 1; i <= nPts; i++) {
		var p = ring[i];
		if (p.y > hiPt.y) {
			hiPt = p;
			hiIndex = i;
		}
	}
	var iPrev = hiIndex;
	do {
		iPrev = iPrev - 1;
		if (iPrev < 0) iPrev = nPts;
	} while (ring[iPrev].equals2D(hiPt) && iPrev !== hiIndex);
	var iNext = hiIndex;
	do {
		iNext = (iNext + 1) % nPts;
	} while (ring[iNext].equals2D(hiPt) && iNext !== hiIndex);
	var prev = ring[iPrev];
	var next = ring[iNext];
	if (prev.equals2D(hiPt) || next.equals2D(hiPt) || prev.equals2D(next)) return false;
	var disc = CGAlgorithms.computeOrientation(prev, hiPt, next);
	var isCCW = false;
	if (disc === 0) {
		isCCW = prev.x > next.x;
	} else {
		isCCW = disc > 0;
	}
	return isCCW;
};
CGAlgorithms.locatePointInRing = function (p, ring) {
	return RayCrossingCounter.locatePointInRing(p, ring);
};
CGAlgorithms.distancePointLinePerpendicular = function (p, A, B) {
	var len2 = (B.x - A.x) * (B.x - A.x) + (B.y - A.y) * (B.y - A.y);
	var s = ((A.y - p.y) * (B.x - A.x) - (A.x - p.x) * (B.y - A.y)) / len2;
	return Math.abs(s) * Math.sqrt(len2);
};
CGAlgorithms.computeOrientation = function (p1, p2, q) {
	return CGAlgorithms.orientationIndex(p1, p2, q);
};
CGAlgorithms.distancePointLine = function () {
	if (arguments.length === 2) {
		let p = arguments[0], line = arguments[1];
		if (line.length === 0) throw new IllegalArgumentException("Line array must contain at least one vertex");
		var minDistance = p.distance(line[0]);
		for (var i = 0; i < line.length - 1; i++) {
			var dist = CGAlgorithms.distancePointLine(p, line[i], line[i + 1]);
			if (dist < minDistance) {
				minDistance = dist;
			}
		}
		return minDistance;
	} else if (arguments.length === 3) {
		let p = arguments[0], A = arguments[1], B = arguments[2];
		if (A.x === B.x && A.y === B.y) return p.distance(A);
		var len2 = (B.x - A.x) * (B.x - A.x) + (B.y - A.y) * (B.y - A.y);
		var r = ((p.x - A.x) * (B.x - A.x) + (p.y - A.y) * (B.y - A.y)) / len2;
		if (r <= 0.0) return p.distance(A);
		if (r >= 1.0) return p.distance(B);
		var s = ((A.y - p.y) * (B.x - A.x) - (A.x - p.x) * (B.y - A.y)) / len2;
		return Math.abs(s) * Math.sqrt(len2);
	}
};
CGAlgorithms.isOnLine = function (p, pt) {
	var lineIntersector = new RobustLineIntersector();
	for (var i = 1; i < pt.length; i++) {
		var p0 = pt[i - 1];
		var p1 = pt[i];
		lineIntersector.computeIntersection(p, p0, p1);
		if (lineIntersector.hasIntersection()) {
			return true;
		}
	}
	return false;
};
CGAlgorithms.CLOCKWISE = -1;
CGAlgorithms.RIGHT = CGAlgorithms.CLOCKWISE;
CGAlgorithms.COUNTERCLOCKWISE = 1;
CGAlgorithms.LEFT = CGAlgorithms.COUNTERCLOCKWISE;
CGAlgorithms.COLLINEAR = 0;
CGAlgorithms.STRAIGHT = CGAlgorithms.COLLINEAR;

function GeometryComponentFilter() {}
extend$1(GeometryComponentFilter.prototype, {
	filter: function (geom) {},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return GeometryComponentFilter;
	}
});

function Geometry() {
	this.envelope = null;
	this.factory = null;
	this.SRID = null;
	this.userData = null;
	let factory = arguments[0];
	this.factory = factory;
	this.SRID = factory.getSRID();
}
extend$1(Geometry.prototype, {
	isGeometryCollection: function () {
		return this.getSortIndex() === Geometry.SORTINDEX_GEOMETRYCOLLECTION;
	},
	getFactory: function () {
		return this.factory;
	},
	getGeometryN: function (n) {
		return this;
	},
	getArea: function () {
		return 0.0;
	},
	isRectangle: function () {
		return false;
	},
	equals: function () {
		if (arguments.length === 1) {
			if (arguments[0] instanceof Geometry) {
				let g = arguments[0];
				if (g === null) return false;
				return this.equalsTopo(g);
			} else if (arguments[0] instanceof Object) {
				let o = arguments[0];
				if (!(o instanceof Geometry)) return false;
				var g = o;
				return this.equalsExact(g);
			}
		}
	},
	equalsExact: function (other) {
		return this === other || this.equalsExact(other, 0);
	},
	geometryChanged: function () {
		this.apply(Geometry.geometryChangedFilter);
	},
	geometryChangedAction: function () {
		this.envelope = null;
	},
	equalsNorm: function (g) {
		if (g === null) return false;
		return this.norm().equalsExact(g.norm());
	},
	getLength: function () {
		return 0.0;
	},
	getNumGeometries: function () {
		return 1;
	},
	compareTo: function () {
		if (arguments.length === 1) {
			let o = arguments[0];
			var other = o;
			if (this.getSortIndex() !== other.getSortIndex()) {
				return this.getSortIndex() - other.getSortIndex();
			}
			if (this.isEmpty() && other.isEmpty()) {
				return 0;
			}
			if (this.isEmpty()) {
				return -1;
			}
			if (other.isEmpty()) {
				return 1;
			}
			return this.compareToSameClass(o);
		} else if (arguments.length === 2) {
			let o = arguments[0], comp = arguments[1];
			var other = o;
			if (this.getSortIndex() !== other.getSortIndex()) {
				return this.getSortIndex() - other.getSortIndex();
			}
			if (this.isEmpty() && other.isEmpty()) {
				return 0;
			}
			if (this.isEmpty()) {
				return -1;
			}
			if (other.isEmpty()) {
				return 1;
			}
			return this.compareToSameClass(o, comp);
		}
	},
	getUserData: function () {
		return this.userData;
	},
	getSRID: function () {
		return this.SRID;
	},
	getEnvelope: function () {
		return this.getFactory().toGeometry(this.getEnvelopeInternal());
	},
	checkNotGeometryCollection: function (g) {
		if (g.getSortIndex() === Geometry.SORTINDEX_GEOMETRYCOLLECTION) {
			throw new IllegalArgumentException("This method does not support GeometryCollection arguments");
		}
	},
	equal: function (a, b, tolerance) {
		if (tolerance === 0) {
			return a.equals(b);
		}
		return a.distance(b) <= tolerance;
	},
	norm: function () {
		var copy = this.copy();
		copy.normalize();
		return copy;
	},
	getPrecisionModel: function () {
		return this.factory.getPrecisionModel();
	},
	getEnvelopeInternal: function () {
		if (this.envelope === null) {
			this.envelope = this.computeEnvelopeInternal();
		}
		return new Envelope(this.envelope);
	},
	setSRID: function (SRID) {
		this.SRID = SRID;
	},
	setUserData: function (userData) {
		this.userData = userData;
	},
	compare: function (a, b) {
		var i = a.iterator();
		var j = b.iterator();
		while (i.hasNext() && j.hasNext()) {
			var aElement = i.next();
			var bElement = j.next();
			var comparison = aElement.compareTo(bElement);
			if (comparison !== 0) {
				return comparison;
			}
		}
		if (i.hasNext()) {
			return 1;
		}
		if (j.hasNext()) {
			return -1;
		}
		return 0;
	},
	hashCode: function () {
		return this.getEnvelopeInternal().hashCode();
	},
	isGeometryCollectionOrDerived: function () {
		if (this.getSortIndex() === Geometry.SORTINDEX_GEOMETRYCOLLECTION || this.getSortIndex() === Geometry.SORTINDEX_MULTIPOINT || this.getSortIndex() === Geometry.SORTINDEX_MULTILINESTRING || this.getSortIndex() === Geometry.SORTINDEX_MULTIPOLYGON) {
			return true;
		}
		return false;
	},
	interfaces_: function () {
		return [Clonable, Comparable, Serializable];
	},
	getClass: function () {
		return Geometry;
	}
});
Geometry.hasNonEmptyElements = function (geometries) {
	for (var i = 0; i < geometries.length; i++) {
		if (!geometries[i].isEmpty()) {
			return true;
		}
	}
	return false;
};
Geometry.hasNullElements = function (array) {
	for (var i = 0; i < array.length; i++) {
		if (array[i] === null) {
			return true;
		}
	}
	return false;
};
Geometry.serialVersionUID = 8763622679187376702;
Geometry.SORTINDEX_POINT = 0;
Geometry.SORTINDEX_MULTIPOINT = 1;
Geometry.SORTINDEX_LINESTRING = 2;
Geometry.SORTINDEX_LINEARRING = 3;
Geometry.SORTINDEX_MULTILINESTRING = 4;
Geometry.SORTINDEX_POLYGON = 5;
Geometry.SORTINDEX_MULTIPOLYGON = 6;
Geometry.SORTINDEX_GEOMETRYCOLLECTION = 7;
Geometry.geometryChangedFilter = {
	interfaces_: function () {
		return [GeometryComponentFilter];
	},
	filter: function (geom) {
		geom.geometryChangedAction();
	}
};

function CoordinateFilter() {}
extend$1(CoordinateFilter.prototype, {
	filter: function (coord) {},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return CoordinateFilter;
	}
});

function BoundaryNodeRule() {}
extend$1(BoundaryNodeRule.prototype, {
	isInBoundary: function (boundaryCount) {},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return BoundaryNodeRule;
	}
});
function Mod2BoundaryNodeRule() {}
extend$1(Mod2BoundaryNodeRule.prototype, {
	isInBoundary: function (boundaryCount) {
		return boundaryCount % 2 === 1;
	},
	interfaces_: function () {
		return [BoundaryNodeRule];
	},
	getClass: function () {
		return Mod2BoundaryNodeRule;
	}
});
function EndPointBoundaryNodeRule() {}
extend$1(EndPointBoundaryNodeRule.prototype, {
	isInBoundary: function (boundaryCount) {
		return boundaryCount > 0;
	},
	interfaces_: function () {
		return [BoundaryNodeRule];
	},
	getClass: function () {
		return EndPointBoundaryNodeRule;
	}
});
function MultiValentEndPointBoundaryNodeRule() {}
extend$1(MultiValentEndPointBoundaryNodeRule.prototype, {
	isInBoundary: function (boundaryCount) {
		return boundaryCount > 1;
	},
	interfaces_: function () {
		return [BoundaryNodeRule];
	},
	getClass: function () {
		return MultiValentEndPointBoundaryNodeRule;
	}
});
function MonoValentEndPointBoundaryNodeRule() {}
extend$1(MonoValentEndPointBoundaryNodeRule.prototype, {
	isInBoundary: function (boundaryCount) {
		return boundaryCount === 1;
	},
	interfaces_: function () {
		return [BoundaryNodeRule];
	},
	getClass: function () {
		return MonoValentEndPointBoundaryNodeRule;
	}
});
BoundaryNodeRule.Mod2BoundaryNodeRule = Mod2BoundaryNodeRule;
BoundaryNodeRule.EndPointBoundaryNodeRule = EndPointBoundaryNodeRule;
BoundaryNodeRule.MultiValentEndPointBoundaryNodeRule = MultiValentEndPointBoundaryNodeRule;
BoundaryNodeRule.MonoValentEndPointBoundaryNodeRule = MonoValentEndPointBoundaryNodeRule;
BoundaryNodeRule.MOD2_BOUNDARY_RULE = new Mod2BoundaryNodeRule();
BoundaryNodeRule.ENDPOINT_BOUNDARY_RULE = new EndPointBoundaryNodeRule();
BoundaryNodeRule.MULTIVALENT_ENDPOINT_BOUNDARY_RULE = new MultiValentEndPointBoundaryNodeRule();
BoundaryNodeRule.MONOVALENT_ENDPOINT_BOUNDARY_RULE = new MonoValentEndPointBoundaryNodeRule();
BoundaryNodeRule.OGC_SFS_BOUNDARY_RULE = BoundaryNodeRule.MOD2_BOUNDARY_RULE;

/**
 * @see http://download.oracle.com/javase/6/docs/api/java/util/Iterator.html
 * @constructor
 * @private
 */
function Iterator() {}

/**
 * Returns true if the iteration has more elements.
 * @return {boolean}
 */
Iterator.prototype.hasNext = function() {};

/**
 * Returns the next element in the iteration.
 * @return {Object}
 */
Iterator.prototype.next = function() {};

/**
 * Removes from the underlying collection the last element returned by the
 * iterator (optional operation).
 */
Iterator.prototype.remove = function() {};

/**
 * @see http://download.oracle.com/javase/6/docs/api/java/util/Collection.html
 *
 * @constructor
 * @private
 */
function Collection() {}

/**
 * Ensures that this collection contains the specified element (optional
 * operation).
 * @param {Object} e
 * @return {boolean}
 */
Collection.prototype.add = function() {};


/**
 * Appends all of the elements in the specified collection to the end of this
 * list, in the order that they are returned by the specified collection's
 * iterator (optional operation).
 * @param {javascript.util.Collection} c
 * @return {boolean}
 */
Collection.prototype.addAll = function() {};


/**
 * Returns true if this collection contains no elements.
 * @return {boolean}
 */
Collection.prototype.isEmpty = function() {};


/**
 * Returns an iterator over the elements in this collection.
 * @return {javascript.util.Iterator}
 */
Collection.prototype.iterator = function() {};


/**
 * Returns an iterator over the elements in this collection.
 * @return {number}
 */
Collection.prototype.size = function() {};


/**
 * Returns an array containing all of the elements in this collection.
 * @return {Array}
 */
Collection.prototype.toArray = function() {};


/**
 * Removes a single instance of the specified element from this collection if it
 * is present. (optional)
 * @param {Object} e
 * @return {boolean}
 */
Collection.prototype.remove = function() {};

/**
 * @param {string=} message Optional message
 * @extends {Error}
 * @constructor
 * @private
 */
function IndexOutOfBoundsException$1(message) {
  this.message = message || '';
}
IndexOutOfBoundsException$1.prototype = new Error();

/**
 * @type {string}
 */
IndexOutOfBoundsException$1.prototype.name = 'IndexOutOfBoundsException';

/**
 * @see http://download.oracle.com/javase/6/docs/api/java/util/List.html
 *
 * @extends {javascript.util.Collection}
 * @constructor
 * @private
 */
function List() { }
List.prototype = Object.create(Collection.prototype);
List.prototype.constructor = List;

/**
 * Returns the element at the specified position in this list.
 * @param {number} index
 * @return {Object}
 */
List.prototype.get = function() { };


/**
 * Replaces the element at the specified position in this list with the
 * specified element (optional operation).
 * @param {number} index
 * @param {Object} e
 * @return {Object}
 */
List.prototype.set = function() { };


/**
 * Returns true if this collection contains no elements.
 * @return {boolean}
 */
List.prototype.isEmpty = function() { };

/**
 * @param {string=} message Optional message
 * @extends {Error}
 * @constructor
 * @private
 */
function NoSuchElementException(message) {
  this.message = message || '';
}
NoSuchElementException.prototype = new Error();


/**
 * @type {string}
 */
NoSuchElementException.prototype.name = 'NoSuchElementException';

/**
 * @param {string=} message Optional message
 * @extends {Error}
 * @constructor
 * @private
 */
function OperationNotSupported(message) {
  this.message = message || '';
}
OperationNotSupported.prototype = new Error();


/**
 * @type {string}
 */
OperationNotSupported.prototype.name = 'OperationNotSupported';

/**
 * @see http://download.oracle.com/javase/6/docs/api/java/util/ArrayList.html
 *
 * @extends List
 * @private
 */
function ArrayList () {
  /**
   * @type {Array}
   * @private
  */
  this.array_ = [];

  if (arguments[0] instanceof Collection) {
    this.addAll(arguments[0]);
  }
}
ArrayList.prototype = Object.create(List.prototype);
ArrayList.prototype.constructor = ArrayList;

ArrayList.prototype.ensureCapacity = function () {};
ArrayList.prototype.interfaces_ = function () { return [List, Collection] };

/**
 * @override
 */
ArrayList.prototype.add = function(e) {
  if (arguments.length === 1) {
    this.array_.push(e);
  } else {
    this.array_.splice(arguments[0], arguments[1]);
  }
  return true
};

ArrayList.prototype.clear = function() {
  this.array_ = [];
};

/**
 * @override
 */
ArrayList.prototype.addAll = function(c) {
  for (var i = c.iterator(); i.hasNext();) {
    this.add(i.next());
  }
  return true;
};


/**
 * @override
 */
ArrayList.prototype.set = function(index, element) {
  var oldElement = this.array_[index];
  this.array_[index] = element;
  return oldElement;
};


/**
 * @override
 */
ArrayList.prototype.iterator = function() {
  return new Iterator_(this);
};


/**
 * @override
 */
ArrayList.prototype.get = function(index) {
  if (index < 0 || index >= this.size()) {
    throw new IndexOutOfBoundsException$1();
  }

  return this.array_[index];
};


/**
 * @override
 */
ArrayList.prototype.isEmpty = function() {
  return this.array_.length === 0;
};


/**
 * @override
 */
ArrayList.prototype.size = function() {
  return this.array_.length;
};


/**
 * @override
 */
ArrayList.prototype.toArray = function() {
  var array = [];

  for (var i = 0, len = this.array_.length; i < len; i++) {
    array.push(this.array_[i]);
  }

  return array;
};


/**
 * @override
 */
ArrayList.prototype.remove = function(o) {
  var found = false;

  for (var i = 0, len = this.array_.length; i < len; i++) {
    if (this.array_[i] === o) {
      this.array_.splice(i, 1);
      found = true;
      break;
    }
  }

  return found;
};



/**
 * @extends {Iterator}
 * @param {ArrayList} arrayList
 * @constructor
 * @private
 */
var Iterator_ = function(arrayList) {
  /**
   * @type {ArrayList}
   * @private
  */
  this.arrayList_ = arrayList;
  /**
   * @type {number}
   * @private
  */
  this.position_ = 0;
};


/**
 * @override
 */
Iterator_.prototype.next = function() {
  if (this.position_ === this.arrayList_.size()) {
    throw new NoSuchElementException();
  }
  return this.arrayList_.get(this.position_++);
};


/**
 * @override
 */
Iterator_.prototype.hasNext = function() {
  if (this.position_ < this.arrayList_.size()) {
    return true;
  } else {
    return false;
  }
};

/**
 * TODO: should be in ListIterator
 * @override
 */
Iterator_.prototype.set = function(element) {
  return this.arrayList_.set(this.position_ - 1, element);
};


/**
 * @override
 */
Iterator_.prototype.remove = function() {
  this.arrayList_.remove(this.arrayList_.get(this.position_));
};

function CoordinateList() {
	ArrayList.apply(this);
	if (arguments.length === 0) {} else if (arguments.length === 1) {
		let coord = arguments[0];
		this.ensureCapacity(coord.length);
		this.add(coord, true);
	} else if (arguments.length === 2) {
		let coord = arguments[0], allowRepeated = arguments[1];
		this.ensureCapacity(coord.length);
		this.add(coord, allowRepeated);
	}
}
inherits(CoordinateList, ArrayList);
extend$1(CoordinateList.prototype, {
	getCoordinate: function (i) {
		return this.get(i);
	},
	addAll: function () {
		if (arguments.length === 2) {
			let coll = arguments[0], allowRepeated = arguments[1];
			var isChanged = false;
			for (var i = coll.iterator(); i.hasNext(); ) {
				this.add(i.next(), allowRepeated);
				isChanged = true;
			}
			return isChanged;
		} else return ArrayList.prototype.addAll.apply(this, arguments);
	},
	clone: function () {
		var clone = ArrayList.prototype.clone.call(this);
		for (var i = 0; i < this.size(); i++) {
			clone.add(i, this.get(i).copy());
		}
		return clone;
	},
	toCoordinateArray: function () {
		return this.toArray(CoordinateList.coordArrayType);
	},
	add: function () {
		if (arguments.length === 1) {
			let coord = arguments[0];
			ArrayList.prototype.add.call(this, coord);
		} else if (arguments.length === 2) {
			if (arguments[0] instanceof Array && typeof arguments[1] === "boolean") {
				let coord = arguments[0], allowRepeated = arguments[1];
				this.add(coord, allowRepeated, true);
				return true;
			} else if (arguments[0] instanceof Coordinate && typeof arguments[1] === "boolean") {
				let coord = arguments[0], allowRepeated = arguments[1];
				if (!allowRepeated) {
					if (this.size() >= 1) {
						var last = this.get(this.size() - 1);
						if (last.equals2D(coord)) return null;
					}
				}
				ArrayList.prototype.add.call(this, coord);
			} else if (arguments[0] instanceof Object && typeof arguments[1] === "boolean") {
				let obj = arguments[0], allowRepeated = arguments[1];
				this.add(obj, allowRepeated);
				return true;
			}
		} else if (arguments.length === 3) {
			if (typeof arguments[2] === "boolean" && (arguments[0] instanceof Array && typeof arguments[1] === "boolean")) {
				let coord = arguments[0], allowRepeated = arguments[1], direction = arguments[2];
				if (direction) {
					for (var i = 0; i < coord.length; i++) {
						this.add(coord[i], allowRepeated);
					}
				} else {
					for (var i = coord.length - 1; i >= 0; i--) {
						this.add(coord[i], allowRepeated);
					}
				}
				return true;
			} else if (typeof arguments[2] === "boolean" && (Number.isInteger(arguments[0]) && arguments[1] instanceof Coordinate)) {
				let i = arguments[0], coord = arguments[1], allowRepeated = arguments[2];
				if (!allowRepeated) {
					var size = this.size();
					if (size > 0) {
						if (i > 0) {
							var prev = this.get(i - 1);
							if (prev.equals2D(coord)) return null;
						}
						if (i < size) {
							var next = this.get(i);
							if (next.equals2D(coord)) return null;
						}
					}
				}
				ArrayList.prototype.add.call(this, i, coord);
			}
		} else if (arguments.length === 4) {
			let coord = arguments[0], allowRepeated = arguments[1], start = arguments[2], end = arguments[3];
			var inc = 1;
			if (start > end) inc = -1;
			for (var i = start; i !== end; i += inc) {
				this.add(coord[i], allowRepeated);
			}
			return true;
		}
	},
	closeRing: function () {
		if (this.size() > 0) this.add(new Coordinate(this.get(0)), false);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return CoordinateList;
	}
});
CoordinateList.coordArrayType = new Array(0).fill(null);

function CoordinateArrays() {}
extend$1(CoordinateArrays.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return CoordinateArrays;
	}
});
CoordinateArrays.isRing = function (pts) {
	if (pts.length < 4) return false;
	if (!pts[0].equals2D(pts[pts.length - 1])) return false;
	return true;
};
CoordinateArrays.ptNotInList = function (testPts, pts) {
	for (var i = 0; i < testPts.length; i++) {
		var testPt = testPts[i];
		if (CoordinateArrays.indexOf(testPt, pts) < 0) return testPt;
	}
	return null;
};
CoordinateArrays.scroll = function (coordinates, firstCoordinate) {
	var i = CoordinateArrays.indexOf(firstCoordinate, coordinates);
	if (i < 0) return null;
	var newCoordinates = new Array(coordinates.length).fill(null);
	System.arraycopy(coordinates, i, newCoordinates, 0, coordinates.length - i);
	System.arraycopy(coordinates, 0, newCoordinates, coordinates.length - i, i);
	System.arraycopy(newCoordinates, 0, coordinates, 0, coordinates.length);
};
CoordinateArrays.equals = function () {
	if (arguments.length === 2) {
		let coord1 = arguments[0], coord2 = arguments[1];
		if (coord1 === coord2) return true;
		if (coord1 === null || coord2 === null) return false;
		if (coord1.length !== coord2.length) return false;
		for (var i = 0; i < coord1.length; i++) {
			if (!coord1[i].equals(coord2[i])) return false;
		}
		return true;
	} else if (arguments.length === 3) {
		let coord1 = arguments[0], coord2 = arguments[1], coordinateComparator = arguments[2];
		if (coord1 === coord2) return true;
		if (coord1 === null || coord2 === null) return false;
		if (coord1.length !== coord2.length) return false;
		for (var i = 0; i < coord1.length; i++) {
			if (coordinateComparator.compare(coord1[i], coord2[i]) !== 0) return false;
		}
		return true;
	}
};
CoordinateArrays.intersection = function (coordinates, env) {
	var coordList = new CoordinateList();
	for (var i = 0; i < coordinates.length; i++) {
		if (env.intersects(coordinates[i])) coordList.add(coordinates[i], true);
	}
	return coordList.toCoordinateArray();
};
CoordinateArrays.hasRepeatedPoints = function (coord) {
	for (var i = 1; i < coord.length; i++) {
		if (coord[i - 1].equals(coord[i])) {
			return true;
		}
	}
	return false;
};
CoordinateArrays.removeRepeatedPoints = function (coord) {
	if (!CoordinateArrays.hasRepeatedPoints(coord)) return coord;
	var coordList = new CoordinateList(coord, false);
	return coordList.toCoordinateArray();
};
CoordinateArrays.reverse = function (coord) {
	var last = coord.length - 1;
	var mid = Math.trunc(last / 2);
	for (var i = 0; i <= mid; i++) {
		var tmp = coord[i];
		coord[i] = coord[last - i];
		coord[last - i] = tmp;
	}
};
CoordinateArrays.removeNull = function (coord) {
	var nonNull = 0;
	for (var i = 0; i < coord.length; i++) {
		if (coord[i] !== null) nonNull++;
	}
	var newCoord = new Array(nonNull).fill(null);
	if (nonNull === 0) return newCoord;
	var j = 0;
	for (var i = 0; i < coord.length; i++) {
		if (coord[i] !== null) newCoord[j++] = coord[i];
	}
	return newCoord;
};
CoordinateArrays.copyDeep = function () {
	if (arguments.length === 1) {
		let coordinates = arguments[0];
		var copy = new Array(coordinates.length).fill(null);
		for (var i = 0; i < coordinates.length; i++) {
			copy[i] = new Coordinate(coordinates[i]);
		}
		return copy;
	} else if (arguments.length === 5) {
		let src = arguments[0], srcStart = arguments[1], dest = arguments[2], destStart = arguments[3], length = arguments[4];
		for (var i = 0; i < length; i++) {
			dest[destStart + i] = new Coordinate(src[srcStart + i]);
		}
	}
};
CoordinateArrays.isEqualReversed = function (pts1, pts2) {
	for (var i = 0; i < pts1.length; i++) {
		var p1 = pts1[i];
		var p2 = pts2[pts1.length - i - 1];
		if (p1.compareTo(p2) !== 0) return false;
	}
	return true;
};
CoordinateArrays.envelope = function (coordinates) {
	var env = new Envelope();
	for (var i = 0; i < coordinates.length; i++) {
		env.expandToInclude(coordinates[i]);
	}
	return env;
};
CoordinateArrays.toCoordinateArray = function (coordList) {
	return coordList.toArray(CoordinateArrays.coordArrayType);
};
CoordinateArrays.atLeastNCoordinatesOrNothing = function (n, c) {
	return c.length >= n ? c : [];
};
CoordinateArrays.indexOf = function (coordinate, coordinates) {
	for (var i = 0; i < coordinates.length; i++) {
		if (coordinate.equals(coordinates[i])) {
			return i;
		}
	}
	return -1;
};
CoordinateArrays.increasingDirection = function (pts) {
	for (var i = 0; i < Math.trunc(pts.length / 2); i++) {
		var j = pts.length - 1 - i;
		var comp = pts[i].compareTo(pts[j]);
		if (comp !== 0) return comp;
	}
	return 1;
};
CoordinateArrays.compare = function (pts1, pts2) {
	var i = 0;
	while (i < pts1.length && i < pts2.length) {
		var compare = pts1[i].compareTo(pts2[i]);
		if (compare !== 0) return compare;
		i++;
	}
	if (i < pts2.length) return -1;
	if (i < pts1.length) return 1;
	return 0;
};
CoordinateArrays.minCoordinate = function (coordinates) {
	var minCoord = null;
	for (var i = 0; i < coordinates.length; i++) {
		if (minCoord === null || minCoord.compareTo(coordinates[i]) > 0) {
			minCoord = coordinates[i];
		}
	}
	return minCoord;
};
CoordinateArrays.extract = function (pts, start, end) {
	start = MathUtil.clamp(start, 0, pts.length);
	end = MathUtil.clamp(end, -1, pts.length);
	var npts = end - start + 1;
	if (end < 0) npts = 0;
	if (start >= pts.length) npts = 0;
	if (end < start) npts = 0;
	var extractPts = new Array(npts).fill(null);
	if (npts === 0) return extractPts;
	var iPts = 0;
	for (var i = start; i <= end; i++) {
		extractPts[iPts++] = pts[i];
	}
	return extractPts;
};
function ForwardComparator() {}
extend$1(ForwardComparator.prototype, {
	compare: function (o1, o2) {
		var pts1 = o1;
		var pts2 = o2;
		return CoordinateArrays.compare(pts1, pts2);
	},
	interfaces_: function () {
		return [Comparator];
	},
	getClass: function () {
		return ForwardComparator;
	}
});
function BidirectionalComparator() {}
extend$1(BidirectionalComparator.prototype, {
	compare: function (o1, o2) {
		var pts1 = o1;
		var pts2 = o2;
		if (pts1.length < pts2.length) return -1;
		if (pts1.length > pts2.length) return 1;
		if (pts1.length === 0) return 0;
		var forwardComp = CoordinateArrays.compare(pts1, pts2);
		var isEqualRev = CoordinateArrays.isEqualReversed(pts1, pts2);
		if (isEqualRev) return 0;
		return forwardComp;
	},
	OLDcompare: function (o1, o2) {
		var pts1 = o1;
		var pts2 = o2;
		if (pts1.length < pts2.length) return -1;
		if (pts1.length > pts2.length) return 1;
		if (pts1.length === 0) return 0;
		var dir1 = CoordinateArrays.increasingDirection(pts1);
		var dir2 = CoordinateArrays.increasingDirection(pts2);
		var i1 = dir1 > 0 ? 0 : pts1.length - 1;
		var i2 = dir2 > 0 ? 0 : pts1.length - 1;
		for (var i = 0; i < pts1.length; i++) {
			var comparePt = pts1[i1].compareTo(pts2[i2]);
			if (comparePt !== 0) return comparePt;
			i1 += dir1;
			i2 += dir2;
		}
		return 0;
	},
	interfaces_: function () {
		return [Comparator];
	},
	getClass: function () {
		return BidirectionalComparator;
	}
});
CoordinateArrays.ForwardComparator = ForwardComparator;
CoordinateArrays.BidirectionalComparator = BidirectionalComparator;
CoordinateArrays.coordArrayType = new Array(0).fill(null);

/**
 * @see http://download.oracle.com/javase/6/docs/api/java/util/Map.html
 *
 * @constructor
 * @private
 */
function Map$1() {}


/**
 * Returns the value to which the specified key is mapped, or null if this map
 * contains no mapping for the key.
 * @param {Object} key
 * @return {Object}
 */
Map$1.prototype.get = function() {};


/**
 * Associates the specified value with the specified key in this map (optional
 * operation).
 * @param {Object} key
 * @param {Object} value
 * @return {Object}
 */
Map$1.prototype.put = function() {};


/**
 * Returns the number of key-value mappings in this map.
 * @return {number}
 */
Map$1.prototype.size = function() {};


/**
 * Returns a Collection view of the values contained in this map.
 * @return {javascript.util.Collection}
 */
Map$1.prototype.values = function() {};

/**
 * Returns a {@link Set} view of the mappings contained in this map.
 * The set is backed by the map, so changes to the map are
 * reflected in the set, and vice-versa.  If the map is modified
 * while an iteration over the set is in progress (except through
 * the iterator's own <tt>remove</tt> operation, or through the
 * <tt>setValue</tt> operation on a map entry returned by the
 * iterator) the results of the iteration are undefined.  The set
 * supports element removal, which removes the corresponding
 * mapping from the map, via the <tt>Iterator.remove</tt>,
 * <tt>Set.remove</tt>, <tt>removeAll</tt>, <tt>retainAll</tt> and
 * <tt>clear</tt> operations.  It does not support the
 * <tt>add</tt> or <tt>addAll</tt> operations.
 *
 * @return {Set} a set view of the mappings contained in this map
 */
Map$1.prototype.entrySet = function() {};

/**
 * @see http://download.oracle.com/javase/6/docs/api/java/util/SortedMap.html
 *
 * @extends {Map}
 * @constructor
 * @private
 */
function SortedMap() {}
SortedMap.prototype = new Map$1();

/**
 * @see http://download.oracle.com/javase/6/docs/api/java/util/Set.html
 *
 * @extends {Collection}
 * @constructor
 * @private
 */
function Set() {}
Set.prototype = new Collection();


/**
 * Returns true if this set contains the specified element. More formally,
 * returns true if and only if this set contains an element e such that (o==null ?
 * e==null : o.equals(e)).
 * @param {Object} e
 * @return {boolean}
 */
Set.prototype.contains = function() {};

/**
 * @see http://docs.oracle.com/javase/6/docs/api/java/util/HashSet.html
 *
 * @extends {javascript.util.Set}
 * @constructor
 * @private
 */
function HashSet() {
  /**
   * @type {Array}
   * @private
  */
  this.array_ = [];

  if (arguments[0] instanceof Collection) {
    this.addAll(arguments[0]);
  }
}
HashSet.prototype = new Set();


/**
 * @override
 */
HashSet.prototype.contains = function(o) {
  for (var i = 0, len = this.array_.length; i < len; i++) {
    var e = this.array_[i];
    if (e === o) {
      return true;
    }
  }
  return false;
};


/**
 * @override
 */
HashSet.prototype.add = function(o) {
  if (this.contains(o)) {
    return false;
  }

  this.array_.push(o);

  return true;
};


/**
 * @override
 */
HashSet.prototype.addAll = function(c) {
  for (var i = c.iterator(); i.hasNext();) {
    this.add(i.next());
  }
  return true;
};


/**
 * @override
 */
HashSet.prototype.remove = function(o) {
  throw new javascript.util.OperationNotSupported();
};


/**
 * @override
 */
HashSet.prototype.size = function() {
  return this.array_.length;
};


/**
 * @override
 */
HashSet.prototype.isEmpty = function() {
  return this.array_.length === 0;
};


/**
 * @override
 */
HashSet.prototype.toArray = function() {
  var array = [];

  for (var i = 0, len = this.array_.length; i < len; i++) {
    array.push(this.array_[i]);
  }

  return array;
};


/**
 * @override
 */
HashSet.prototype.iterator = function() {
  return new Iterator_$1(this);
};



/**
 * @extends {Iterator}
 * @param {HashSet} hashSet
 * @constructor
 * @private
 */
var Iterator_$1 = function(hashSet) {
  /**
   * @type {HashSet}
   * @private
   */
  this.hashSet_ = hashSet;
  /**
   * @type {number}
   * @private
   */
  this.position_ = 0;
};


/**
 * @override
 */
Iterator_$1.prototype.next = function() {
  if (this.position_ === this.hashSet_.size()) {
    throw new NoSuchElementException();
  }
  return this.hashSet_.array_[this.position_++];
};


/**
 * @override
 */
Iterator_$1.prototype.hasNext = function() {
  if (this.position_ < this.hashSet_.size()) {
    return true;
  } else {
    return false;
  }
};


/**
 * @override
 */
Iterator_$1.prototype.remove = function() {
  throw new OperationNotSupported();
};

const BLACK = 0;
const RED = 1;
function colorOf (p) { return (p == null ? BLACK : p.color) }
function parentOf (p) { return (p == null ? null : p.parent) }
function setColor (p, c) { if (p !== null) p.color = c; }
function leftOf (p) { return (p == null ? null : p.left) }
function rightOf (p) { return (p == null ? null : p.right) }

/**
 * @see http://download.oracle.com/javase/6/docs/api/java/util/TreeMap.html
 *
 * @extends {SortedMap}
 * @constructor
 * @private
 */
function TreeMap() {
  /**
   * @type {Object}
   * @private
   */
  this.root_ = null;
  /**
   * @type {number}
   * @private
  */
  this.size_ = 0;
}
TreeMap.prototype = new SortedMap();


/**
 * @override
 */
TreeMap.prototype.get = function(key) {
  var p = this.root_;
  while (p !== null) {
    var cmp = key['compareTo'](p.key);
    if (cmp < 0) {
      p = p.left;
    } else if (cmp > 0) {
      p = p.right;
    } else {
      return p.value;
    }
  }
  return null;
};


/**
 * @override
 */
TreeMap.prototype.put = function(key, value) {
  if (this.root_ === null) {
    this.root_ = {
      key: key,
      value: value,
      left: null,
      right: null,
      parent: null,
      color: BLACK,
      getValue() { return this.value },
      getKey() { return this.key }
    };
    this.size_ = 1;
    return null;
  }
  var t = this.root_, parent, cmp;
  do {
    parent = t;
    cmp = key['compareTo'](t.key);
    if (cmp < 0) {
      t = t.left;
    } else if (cmp > 0) {
      t = t.right;
    } else {
      var oldValue = t.value;
      t.value = value;
      return oldValue;
    }
  } while (t !== null);
  var e = {
    key: key,
    left: null,
    right: null,
    value: value,
    parent: parent,
    color: BLACK,
    getValue() { return this.value },
    getKey() { return this.key }
  };
  if (cmp < 0) {
    parent.left = e;
  } else {
    parent.right = e;
  }
  this.fixAfterInsertion(e);
  this.size_++;
  return null;
};


/**
 * @param {Object} x
 */
TreeMap.prototype.fixAfterInsertion = function(x) {
  x.color = RED;
  while (x != null && x != this.root_ && x.parent.color == RED) {
    if (parentOf(x) == leftOf(parentOf(parentOf(x)))) {
      var y = rightOf(parentOf(parentOf(x)));
      if (colorOf(y) == RED) {
        setColor(parentOf(x), BLACK);
        setColor(y, BLACK);
        setColor(parentOf(parentOf(x)), RED);
        x = parentOf(parentOf(x));
      } else {
        if (x == rightOf(parentOf(x))) {
          x = parentOf(x);
          this.rotateLeft(x);
        }
        setColor(parentOf(x), BLACK);
        setColor(parentOf(parentOf(x)), RED);
        this.rotateRight(parentOf(parentOf(x)));
      }
    } else {
      var y = leftOf(parentOf(parentOf(x)));
      if (colorOf(y) == RED) {
        setColor(parentOf(x), BLACK);
        setColor(y, BLACK);
        setColor(parentOf(parentOf(x)), RED);
        x = parentOf(parentOf(x));
      } else {
        if (x == leftOf(parentOf(x))) {
          x = parentOf(x);
          this.rotateRight(x);
        }
        setColor(parentOf(x), BLACK);
        setColor(parentOf(parentOf(x)), RED);
        this.rotateLeft(parentOf(parentOf(x)));
      }
    }
  }
  this.root_.color = BLACK;
};


/**
 * @override
 */
TreeMap.prototype.values = function() {
  var arrayList = new ArrayList();
  var p = this.getFirstEntry();
  if (p !== null) {
    arrayList.add(p.value);
    while ((p = TreeMap.successor(p)) !== null) {
      arrayList.add(p.value);
    }
  }
  return arrayList;
};


/**
 * @override
 */
TreeMap.prototype.entrySet = function() {
  var hashSet = new HashSet();
  var p = this.getFirstEntry();
  if (p !== null) {
    hashSet.add(p);
    while ((p = TreeMap.successor(p)) !== null) {
      hashSet.add(p);
    }
  }
  return hashSet;
};


/**
 * @param {Object} p
 */
TreeMap.prototype.rotateLeft = function(p) {
  if (p != null) {
    var r = p.right;
    p.right = r.left;
    if (r.left != null)
      r.left.parent = p;
    r.parent = p.parent;
    if (p.parent == null)
      this.root_ = r;
    else if (p.parent.left == p)
      p.parent.left = r;
    else
      p.parent.right = r;
    r.left = p;
    p.parent = r;
  }
};


/**
 * @param {Object} p
 */
TreeMap.prototype.rotateRight = function(p) {
  if (p != null) {
    var l = p.left;
    p.left = l.right;
    if (l.right != null) l.right.parent = p;
    l.parent = p.parent;
    if (p.parent == null)
      this.root_ = l;
    else if (p.parent.right == p)
      p.parent.right = l;
    else p.parent.left = l;
    l.right = p;
    p.parent = l;
  }
};


/**
 * @return {Object}
 */
TreeMap.prototype.getFirstEntry = function() {
  var p = this.root_;
  if (p != null) {
    while (p.left != null) {
      p = p.left;
    }
  }
  return p;
};


/**
 * @param {Object} t
 * @return {Object}
 * @private
 */
TreeMap.successor = function(t) {
  if (t === null)
    return null;
  else if (t.right !== null) {
    var p = t.right;
    while (p.left !== null) {
      p = p.left;
    }
    return p;
  } else {
    var p = t.parent;
    var ch = t;
    while (p !== null && ch === p.right) {
      ch = p;
      p = p.parent;
    }
    return p;
  }
};


/**
 * @override
 */
TreeMap.prototype.size = function() {
  return this.size_;
};

function Lineal() {}
extend$1(Lineal.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Lineal;
	}
});

/**
 * @see http://download.oracle.com/javase/6/docs/api/java/util/SortedSet.html
 *
 * @extends {Set}
 * @constructor
 * @private
 */
function SortedSet() {}
SortedSet.prototype = new Set();

/**
 * @see http://download.oracle.com/javase/6/docs/api/java/util/TreeSet.html
 *
 * @extends {SortedSet}
 * @constructor
 * @private
 */
function TreeSet() {
  /**
   * @type {Array}
   * @private
  */
  this.array_ = [];

  if (arguments[0] instanceof Collection) {
    this.addAll(arguments[0]);
  }
}
TreeSet.prototype = new SortedSet();


/**
 * @override
 */
TreeSet.prototype.contains = function(o) {
  for (var i = 0, len = this.array_.length; i < len; i++) {
    var e = this.array_[i];
    if (e['compareTo'](o) === 0) {
      return true;
    }
  }
  return false;
};


/**
 * @override
 */
TreeSet.prototype.add = function(o) {
  if (this.contains(o)) {
    return false;
  }

  for (var i = 0, len = this.array_.length; i < len; i++) {
    var e = this.array_[i];
    if (e['compareTo'](o) === 1) {
      this.array_.splice(i, 0, o);
      return true;
    }
  }

  this.array_.push(o);

  return true;
};


/**
 * @override
 */
TreeSet.prototype.addAll = function(c) {
  for (var i = c.iterator(); i.hasNext();) {
    this.add(i.next());
  }
  return true;
};


/**
 * @override
 */
TreeSet.prototype.remove = function(e) {
  throw new OperationNotSupported();
};


/**
 * @override
 */
TreeSet.prototype.size = function() {
  return this.array_.length;
};


/**
 * @override
 */
TreeSet.prototype.isEmpty = function() {
  return this.array_.length === 0;
};


/**
 * @override
 */
TreeSet.prototype.toArray = function() {
  var array = [];

  for (var i = 0, len = this.array_.length; i < len; i++) {
    array.push(this.array_[i]);
  }

  return array;
};


/**
 * @override
 */
TreeSet.prototype.iterator = function() {
  return new Iterator_$2(this);
};



/**
 * @extends {javascript.util.Iterator}
 * @param {javascript.util.TreeSet} treeSet
 * @constructor
 * @private
 */
var Iterator_$2 = function(treeSet) {
  /**
   * @type {javascript.util.TreeSet}
   * @private
   */
  this.treeSet_ = treeSet;
  /**
   * @type {number}
   * @private
   */
  this.position_ = 0;
};


/**
 * @override
 */
Iterator_$2.prototype.next = function() {
  if (this.position_ === this.treeSet_.size()) {
    throw new NoSuchElementException();
  }
  return this.treeSet_.array_[this.position_++];
};


/**
 * @override
 */
Iterator_$2.prototype.hasNext = function() {
  if (this.position_ < this.treeSet_.size()) {
    return true;
  } else {
    return false;
  }
};


/**
 * @override
 */
Iterator_$2.prototype.remove = function() {
  throw new OperationNotSupported();
};

/**
 * @see http://download.oracle.com/javase/6/docs/api/java/util/Arrays.html
 *
 * @constructor
 * @private
 */
function Arrays() {}

/**
 */
Arrays.sort = function() {
  var a = arguments[0], i, t, comparator, compare;
  if (arguments.length === 1) {
    compare = function(a, b) {
      return a.compareTo(b);
    };
    a.sort(compare);
    return;
  } else if (arguments.length === 2) {
    comparator = arguments[1];
    compare = function(a, b) {
      return comparator['compare'](a, b);
    };
    a.sort(compare);
  } else if (arguments.length === 3) {
    t = a.slice(arguments[1], arguments[2]);
    t.sort();
    var r = a.slice(0, arguments[1]).concat(t, a.slice(arguments[2], a.length));
    a.splice(0, a.length);
    for (i = 0; i < r.length; i++) {
      a.push(r[i]);
    }
    return;
  } else if (arguments.length === 4) {
    t = a.slice(arguments[1], arguments[2]);
    comparator = arguments[3];
    compare = function(a, b) {
      return comparator['compare'](a, b);
    };
    t.sort(compare);
    r = a.slice(0, arguments[1]).concat(t, a.slice(arguments[2], a.length));
    a.splice(0, a.length);
    for (i = 0; i < r.length; i++) {
      a.push(r[i]);
    }
    return;
  }
};


/**
 * @param {Array} array
 * @return {ArrayList}
 */
Arrays.asList = function(array) {
  var arrayList = new ArrayList();
  for (var i = 0, len = array.length; i < len; i++) {
    arrayList.add(array[i]);
  }
  return arrayList;
};

function Dimension() {}
extend$1(Dimension.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Dimension;
	}
});
Dimension.toDimensionSymbol = function (dimensionValue) {
	switch (dimensionValue) {
		case Dimension.FALSE:
			return Dimension.SYM_FALSE;
		case Dimension.TRUE:
			return Dimension.SYM_TRUE;
		case Dimension.DONTCARE:
			return Dimension.SYM_DONTCARE;
		case Dimension.P:
			return Dimension.SYM_P;
		case Dimension.L:
			return Dimension.SYM_L;
		case Dimension.A:
			return Dimension.SYM_A;
	}
	throw new IllegalArgumentException("Unknown dimension value: " + dimensionValue);
};
Dimension.toDimensionValue = function (dimensionSymbol) {
	switch (Character.toUpperCase(dimensionSymbol)) {
		case Dimension.SYM_FALSE:
			return Dimension.FALSE;
		case Dimension.SYM_TRUE:
			return Dimension.TRUE;
		case Dimension.SYM_DONTCARE:
			return Dimension.DONTCARE;
		case Dimension.SYM_P:
			return Dimension.P;
		case Dimension.SYM_L:
			return Dimension.L;
		case Dimension.SYM_A:
			return Dimension.A;
	}
	throw new IllegalArgumentException("Unknown dimension symbol: " + dimensionSymbol);
};
Dimension.P = 0;
Dimension.L = 1;
Dimension.A = 2;
Dimension.FALSE = -1;
Dimension.TRUE = -2;
Dimension.DONTCARE = -3;
Dimension.SYM_FALSE = 'F';
Dimension.SYM_TRUE = 'T';
Dimension.SYM_DONTCARE = '*';
Dimension.SYM_P = '0';
Dimension.SYM_L = '1';
Dimension.SYM_A = '2';

function GeometryFilter() {}
extend$1(GeometryFilter.prototype, {
	filter: function (geom) {},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return GeometryFilter;
	}
});

function CoordinateSequenceFilter() {}
extend$1(CoordinateSequenceFilter.prototype, {
	filter: function (seq, i) {},
	isDone: function () {},
	isGeometryChanged: function () {},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return CoordinateSequenceFilter;
	}
});

function GeometryCollection() {
	this.geometries = null;
	let geometries = arguments[0], factory = arguments[1];
	Geometry.call(this, factory);
	if (geometries === null) {
		geometries = [];
	}
	if (Geometry.hasNullElements(geometries)) {
		throw new IllegalArgumentException("geometries must not contain null elements");
	}
	this.geometries = geometries;
}
inherits(GeometryCollection, Geometry);
extend$1(GeometryCollection.prototype, {
	computeEnvelopeInternal: function () {
		var envelope = new Envelope();
		for (var i = 0; i < this.geometries.length; i++) {
			envelope.expandToInclude(this.geometries[i].getEnvelopeInternal());
		}
		return envelope;
	},
	getGeometryN: function (n) {
		return this.geometries[n];
	},
	getSortIndex: function () {
		return Geometry.SORTINDEX_GEOMETRYCOLLECTION;
	},
	getCoordinates: function () {
		var coordinates = new Array(this.getNumPoints()).fill(null);
		var k = -1;
		for (var i = 0; i < this.geometries.length; i++) {
			var childCoordinates = this.geometries[i].getCoordinates();
			for (var j = 0; j < childCoordinates.length; j++) {
				k++;
				coordinates[k] = childCoordinates[j];
			}
		}
		return coordinates;
	},
	getArea: function () {
		var area = 0.0;
		for (var i = 0; i < this.geometries.length; i++) {
			area += this.geometries[i].getArea();
		}
		return area;
	},
	equalsExact: function () {
		if (arguments.length === 2) {
			let other = arguments[0], tolerance = arguments[1];
			if (!this.isEquivalentClass(other)) {
				return false;
			}
			var otherCollection = other;
			if (this.geometries.length !== otherCollection.geometries.length) {
				return false;
			}
			for (var i = 0; i < this.geometries.length; i++) {
				if (!this.geometries[i].equalsExact(otherCollection.geometries[i], tolerance)) {
					return false;
				}
			}
			return true;
		} else return Geometry.prototype.equalsExact.apply(this, arguments);
	},
	normalize: function () {
		for (var i = 0; i < this.geometries.length; i++) {
			this.geometries[i].normalize();
		}
		Arrays.sort(this.geometries);
	},
	getCoordinate: function () {
		if (this.isEmpty()) return null;
		return this.geometries[0].getCoordinate();
	},
	getBoundaryDimension: function () {
		var dimension = Dimension.FALSE;
		for (var i = 0; i < this.geometries.length; i++) {
			dimension = Math.max(dimension, this.geometries[i].getBoundaryDimension());
		}
		return dimension;
	},
	getDimension: function () {
		var dimension = Dimension.FALSE;
		for (var i = 0; i < this.geometries.length; i++) {
			dimension = Math.max(dimension, this.geometries[i].getDimension());
		}
		return dimension;
	},
	getLength: function () {
		var sum = 0.0;
		for (var i = 0; i < this.geometries.length; i++) {
			sum += this.geometries[i].getLength();
		}
		return sum;
	},
	getNumPoints: function () {
		var numPoints = 0;
		for (var i = 0; i < this.geometries.length; i++) {
			numPoints += this.geometries[i].getNumPoints();
		}
		return numPoints;
	},
	getNumGeometries: function () {
		return this.geometries.length;
	},
	reverse: function () {
		var n = this.geometries.length;
		var revGeoms = new Array(n).fill(null);
		for (var i = 0; i < this.geometries.length; i++) {
			revGeoms[i] = this.geometries[i].reverse();
		}
		return this.getFactory().createGeometryCollection(revGeoms);
	},
	compareToSameClass: function () {
		if (arguments.length === 1) {
			let o = arguments[0];
			var theseElements = new TreeSet(Arrays.asList(this.geometries));
			var otherElements = new TreeSet(Arrays.asList(o.geometries));
			return this.compare(theseElements, otherElements);
		} else if (arguments.length === 2) {
			let o = arguments[0], comp = arguments[1];
			var gc = o;
			var n1 = this.getNumGeometries();
			var n2 = gc.getNumGeometries();
			var i = 0;
			while (i < n1 && i < n2) {
				var thisGeom = this.getGeometryN(i);
				var otherGeom = gc.getGeometryN(i);
				var holeComp = thisGeom.compareToSameClass(otherGeom, comp);
				if (holeComp !== 0) return holeComp;
				i++;
			}
			if (i < n1) return 1;
			if (i < n2) return -1;
			return 0;
		}
	},
	apply: function () {
		if (hasInterface(arguments[0], CoordinateFilter)) {
			let filter = arguments[0];
			for (var i = 0; i < this.geometries.length; i++) {
				this.geometries[i].apply(filter);
			}
		} else if (hasInterface(arguments[0], CoordinateSequenceFilter)) {
			let filter = arguments[0];
			if (this.geometries.length === 0) return null;
			for (var i = 0; i < this.geometries.length; i++) {
				this.geometries[i].apply(filter);
				if (filter.isDone()) {
					break;
				}
			}
			if (filter.isGeometryChanged()) this.geometryChanged();
		} else if (hasInterface(arguments[0], GeometryFilter)) {
			let filter = arguments[0];
			filter.filter(this);
			for (var i = 0; i < this.geometries.length; i++) {
				this.geometries[i].apply(filter);
			}
		} else if (hasInterface(arguments[0], GeometryComponentFilter)) {
			let filter = arguments[0];
			filter.filter(this);
			for (var i = 0; i < this.geometries.length; i++) {
				this.geometries[i].apply(filter);
			}
		}
	},
	getBoundary: function () {
		this.checkNotGeometryCollection(this);
		Assert.shouldNeverReachHere();
		return null;
	},
	clone: function () {
		var gc = Geometry.prototype.clone.call(this);
		gc.geometries = new Array(this.geometries.length).fill(null);
		for (var i = 0; i < this.geometries.length; i++) {
			gc.geometries[i] = this.geometries[i].clone();
		}
		return gc;
	},
	getGeometryType: function () {
		return "GeometryCollection";
	},
	copy: function () {
		var geometries = new Array(this.geometries.length).fill(null);
		for (var i = 0; i < geometries.length; i++) {
			geometries[i] = this.geometries[i].copy();
		}
		return new GeometryCollection(geometries, this.factory);
	},
	isEmpty: function () {
		for (var i = 0; i < this.geometries.length; i++) {
			if (!this.geometries[i].isEmpty()) {
				return false;
			}
		}
		return true;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return GeometryCollection;
	}
});
GeometryCollection.serialVersionUID = -5694727726395021467;

function MultiLineString() {
	let lineStrings = arguments[0], factory = arguments[1];
	GeometryCollection.call(this, lineStrings, factory);
}
inherits(MultiLineString, GeometryCollection);
extend$1(MultiLineString.prototype, {
	getSortIndex: function () {
		return Geometry.SORTINDEX_MULTILINESTRING;
	},
	equalsExact: function () {
		if (arguments.length === 2) {
			let other = arguments[0], tolerance = arguments[1];
			if (!this.isEquivalentClass(other)) {
				return false;
			}
			return GeometryCollection.prototype.equalsExact.call(this, other, tolerance);
		} else return GeometryCollection.prototype.equalsExact.apply(this, arguments);
	},
	getBoundaryDimension: function () {
		if (this.isClosed()) {
			return Dimension.FALSE;
		}
		return 0;
	},
	isClosed: function () {
		if (this.isEmpty()) {
			return false;
		}
		for (var i = 0; i < this.geometries.length; i++) {
			if (!this.geometries[i].isClosed()) {
				return false;
			}
		}
		return true;
	},
	getDimension: function () {
		return 1;
	},
	reverse: function () {
		var nLines = this.geometries.length;
		var revLines = new Array(nLines).fill(null);
		for (var i = 0; i < this.geometries.length; i++) {
			revLines[nLines - 1 - i] = this.geometries[i].reverse();
		}
		return this.getFactory().createMultiLineString(revLines);
	},
	getBoundary: function () {
		return new BoundaryOp(this).getBoundary();
	},
	getGeometryType: function () {
		return "MultiLineString";
	},
	copy: function () {
		var lineStrings = new Array(this.geometries.length).fill(null);
		for (var i = 0; i < lineStrings.length; i++) {
			lineStrings[i] = this.geometries[i].copy();
		}
		return new MultiLineString(lineStrings, this.factory);
	},
	interfaces_: function () {
		return [Lineal];
	},
	getClass: function () {
		return MultiLineString;
	}
});
MultiLineString.serialVersionUID = 8166665132445433741;

function BoundaryOp() {
	this.geom = null;
	this.geomFact = null;
	this.bnRule = null;
	this.endpointMap = null;
	if (arguments.length === 1) {
		let geom = arguments[0];
		BoundaryOp.call(this, geom, BoundaryNodeRule.MOD2_BOUNDARY_RULE);
	} else if (arguments.length === 2) {
		let geom = arguments[0], bnRule = arguments[1];
		this.geom = geom;
		this.geomFact = geom.getFactory();
		this.bnRule = bnRule;
	}
}
extend$1(BoundaryOp.prototype, {
	boundaryMultiLineString: function (mLine) {
		if (this.geom.isEmpty()) {
			return this.getEmptyMultiPoint();
		}
		var bdyPts = this.computeBoundaryCoordinates(mLine);
		if (bdyPts.length === 1) {
			return this.geomFact.createPoint(bdyPts[0]);
		}
		return this.geomFact.createMultiPointFromCoords(bdyPts);
	},
	getBoundary: function () {
		if (this.geom instanceof LineString) return this.boundaryLineString(this.geom);
		if (this.geom instanceof MultiLineString) return this.boundaryMultiLineString(this.geom);
		return this.geom.getBoundary();
	},
	boundaryLineString: function (line) {
		if (this.geom.isEmpty()) {
			return this.getEmptyMultiPoint();
		}
		if (line.isClosed()) {
			var closedEndpointOnBoundary = this.bnRule.isInBoundary(2);
			if (closedEndpointOnBoundary) {
				return line.getStartPoint();
			} else {
				return this.geomFact.createMultiPoint();
			}
		}
		return this.geomFact.createMultiPoint([line.getStartPoint(), line.getEndPoint()]);
	},
	getEmptyMultiPoint: function () {
		return this.geomFact.createMultiPoint();
	},
	computeBoundaryCoordinates: function (mLine) {
		var bdyPts = new ArrayList();
		this.endpointMap = new TreeMap();
		for (var i = 0; i < mLine.getNumGeometries(); i++) {
			var line = mLine.getGeometryN(i);
			if (line.getNumPoints() === 0) continue;
			this.addEndpoint(line.getCoordinateN(0));
			this.addEndpoint(line.getCoordinateN(line.getNumPoints() - 1));
		}
		for (var it = this.endpointMap.entrySet().iterator(); it.hasNext(); ) {
			var entry = it.next();
			var counter = entry.getValue();
			var valence = counter.count;
			if (this.bnRule.isInBoundary(valence)) {
				bdyPts.add(entry.getKey());
			}
		}
		return CoordinateArrays.toCoordinateArray(bdyPts);
	},
	addEndpoint: function (pt) {
		var counter = this.endpointMap.get(pt);
		if (counter === null) {
			counter = new Counter();
			this.endpointMap.put(pt, counter);
		}
		counter.count++;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return BoundaryOp;
	}
});
BoundaryOp.getBoundary = function () {
	if (arguments.length === 1) {
		let g = arguments[0];
		var bop = new BoundaryOp(g);
		return bop.getBoundary();
	} else if (arguments.length === 2) {
		let g = arguments[0], bnRule = arguments[1];
		var bop = new BoundaryOp(g, bnRule);
		return bop.getBoundary();
	}
};
function Counter() {
	this.count = null;
}
extend$1(Counter.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Counter;
	}
});

function PrintStream () {}

function StringReader () {}

function DecimalFormat () {}

function ByteArrayOutputStream () {}

function IOException () {}

function LineNumberReader () {}

function StringUtil() {}
extend$1(StringUtil.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return StringUtil;
	}
});
StringUtil.chars = function (c, n) {
	var ch = new Array(n).fill(null);
	for (var i = 0; i < n; i++) {
		ch[i] = c;
	}
	return new String(ch);
};
StringUtil.getStackTrace = function () {
	if (arguments.length === 1) {
		let t = arguments[0];
		var os = new ByteArrayOutputStream();
		var ps = new PrintStream(os);
		t.printStackTrace(ps);
		return os.toString();
	} else if (arguments.length === 2) {
		let t = arguments[0], depth = arguments[1];
		var stackTrace = "";
		var stringReader = new StringReader(StringUtil.getStackTrace(t));
		var lineNumberReader = new LineNumberReader(stringReader);
		for (var i = 0; i < depth; i++) {
			try {
				stackTrace += lineNumberReader.readLine() + StringUtil.NEWLINE;
			} catch (e) {
				if (e instanceof IOException) {
					Assert.shouldNeverReachHere();
				} else throw e;
			} finally {}
		}
		return stackTrace;
	}
};
StringUtil.split = function (s, separator) {
	var separatorlen = separator.length;
	var tokenList = new ArrayList();
	var tmpString = "" + s;
	var pos = tmpString.indexOf(separator);
	while (pos >= 0) {
		var token = tmpString.substring(0, pos);
		tokenList.add(token);
		tmpString = tmpString.substring(pos + separatorlen);
		pos = tmpString.indexOf(separator);
	}
	if (tmpString.length > 0) tokenList.add(tmpString);
	var res = new Array(tokenList.size()).fill(null);
	for (var i = 0; i < res.length; i++) {
		res[i] = tokenList.get(i);
	}
	return res;
};
StringUtil.toString = function () {
	if (arguments.length === 1) {
		let d = arguments[0];
		return StringUtil.SIMPLE_ORDINATE_FORMAT.format(d);
	}
};
StringUtil.spaces = function (n) {
	return StringUtil.chars(' ', n);
};
StringUtil.NEWLINE = System.getProperty("line.separator");
StringUtil.SIMPLE_ORDINATE_FORMAT = new DecimalFormat("0.#");

function CoordinateSequences() {}
extend$1(CoordinateSequences.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return CoordinateSequences;
	}
});
CoordinateSequences.copyCoord = function (src, srcPos, dest, destPos) {
	var minDim = Math.min(src.getDimension(), dest.getDimension());
	for (var dim = 0; dim < minDim; dim++) {
		dest.setOrdinate(destPos, dim, src.getOrdinate(srcPos, dim));
	}
};
CoordinateSequences.isRing = function (seq) {
	var n = seq.size();
	if (n === 0) return true;
	if (n <= 3) return false;
	return seq.getOrdinate(0, CoordinateSequence.X) === seq.getOrdinate(n - 1, CoordinateSequence.X) && seq.getOrdinate(0, CoordinateSequence.Y) === seq.getOrdinate(n - 1, CoordinateSequence.Y);
};
CoordinateSequences.isEqual = function (cs1, cs2) {
	var cs1Size = cs1.size();
	var cs2Size = cs2.size();
	if (cs1Size !== cs2Size) return false;
	var dim = Math.min(cs1.getDimension(), cs2.getDimension());
	for (var i = 0; i < cs1Size; i++) {
		for (var d = 0; d < dim; d++) {
			var v1 = cs1.getOrdinate(i, d);
			var v2 = cs2.getOrdinate(i, d);
			if (cs1.getOrdinate(i, d) === cs2.getOrdinate(i, d)) continue;
			if (Double.isNaN(v1) && Double.isNaN(v2)) continue;
			return false;
		}
	}
	return true;
};
CoordinateSequences.extend = function (fact, seq, size) {
	var newseq = fact.create(size, seq.getDimension());
	var n = seq.size();
	CoordinateSequences.copy(seq, 0, newseq, 0, n);
	if (n > 0) {
		for (var i = n; i < size; i++) CoordinateSequences.copy(seq, n - 1, newseq, i, 1);
	}
	return newseq;
};
CoordinateSequences.reverse = function (seq) {
	var last = seq.size() - 1;
	var mid = Math.trunc(last / 2);
	for (var i = 0; i <= mid; i++) {
		CoordinateSequences.swap(seq, i, last - i);
	}
};
CoordinateSequences.swap = function (seq, i, j) {
	if (i === j) return null;
	for (var dim = 0; dim < seq.getDimension(); dim++) {
		var tmp = seq.getOrdinate(i, dim);
		seq.setOrdinate(i, dim, seq.getOrdinate(j, dim));
		seq.setOrdinate(j, dim, tmp);
	}
};
CoordinateSequences.copy = function (src, srcPos, dest, destPos, length) {
	for (var i = 0; i < length; i++) {
		CoordinateSequences.copyCoord(src, srcPos + i, dest, destPos + i);
	}
};
CoordinateSequences.toString = function () {
	if (arguments.length === 1) {
		let cs = arguments[0];
		var size = cs.size();
		if (size === 0) return "()";
		var dim = cs.getDimension();
		var buf = new StringBuffer();
		buf.append('(');
		for (var i = 0; i < size; i++) {
			if (i > 0) buf.append(" ");
			for (var d = 0; d < dim; d++) {
				if (d > 0) buf.append(",");
				buf.append(StringUtil.toString(cs.getOrdinate(i, d)));
			}
		}
		buf.append(')');
		return buf.toString();
	}
};
CoordinateSequences.ensureValidRing = function (fact, seq) {
	var n = seq.size();
	if (n === 0) return seq;
	if (n <= 3) return CoordinateSequences.createClosedRing(fact, seq, 4);
	var isClosed = seq.getOrdinate(0, CoordinateSequence.X) === seq.getOrdinate(n - 1, CoordinateSequence.X) && seq.getOrdinate(0, CoordinateSequence.Y) === seq.getOrdinate(n - 1, CoordinateSequence.Y);
	if (isClosed) return seq;
	return CoordinateSequences.createClosedRing(fact, seq, n + 1);
};
CoordinateSequences.createClosedRing = function (fact, seq, size) {
	var newseq = fact.create(size, seq.getDimension());
	var n = seq.size();
	CoordinateSequences.copy(seq, 0, newseq, 0, n);
	for (var i = n; i < size; i++) CoordinateSequences.copy(seq, 0, newseq, i, 1);
	return newseq;
};

function LineString() {
	this.points = null;
	let points = arguments[0], factory = arguments[1];
	Geometry.call(this, factory);
	this.init(points);
}
inherits(LineString, Geometry);
extend$1(LineString.prototype, {
	computeEnvelopeInternal: function () {
		if (this.isEmpty()) {
			return new Envelope();
		}
		return this.points.expandEnvelope(new Envelope());
	},
	isRing: function () {
		return this.isClosed() && this.isSimple();
	},
	getSortIndex: function () {
		return Geometry.SORTINDEX_LINESTRING;
	},
	getCoordinates: function () {
		return this.points.toCoordinateArray();
	},
	equalsExact: function () {
		if (arguments.length === 2) {
			let other = arguments[0], tolerance = arguments[1];
			if (!this.isEquivalentClass(other)) {
				return false;
			}
			var otherLineString = other;
			if (this.points.size() !== otherLineString.points.size()) {
				return false;
			}
			for (var i = 0; i < this.points.size(); i++) {
				if (!this.equal(this.points.getCoordinate(i), otherLineString.points.getCoordinate(i), tolerance)) {
					return false;
				}
			}
			return true;
		} else return Geometry.prototype.equalsExact.apply(this, arguments);
	},
	normalize: function () {
		for (var i = 0; i < Math.trunc(this.points.size() / 2); i++) {
			var j = this.points.size() - 1 - i;
			if (!this.points.getCoordinate(i).equals(this.points.getCoordinate(j))) {
				if (this.points.getCoordinate(i).compareTo(this.points.getCoordinate(j)) > 0) {
					CoordinateSequences.reverse(this.points);
				}
				return null;
			}
		}
	},
	getCoordinate: function () {
		if (this.isEmpty()) return null;
		return this.points.getCoordinate(0);
	},
	getBoundaryDimension: function () {
		if (this.isClosed()) {
			return Dimension.FALSE;
		}
		return 0;
	},
	isClosed: function () {
		if (this.isEmpty()) {
			return false;
		}
		return this.getCoordinateN(0).equals2D(this.getCoordinateN(this.getNumPoints() - 1));
	},
	getEndPoint: function () {
		if (this.isEmpty()) {
			return null;
		}
		return this.getPointN(this.getNumPoints() - 1);
	},
	getDimension: function () {
		return 1;
	},
	getLength: function () {
		return CGAlgorithms.computeLength(this.points);
	},
	getNumPoints: function () {
		return this.points.size();
	},
	reverse: function () {
		var seq = this.points.copy();
		CoordinateSequences.reverse(seq);
		var revLine = this.getFactory().createLineString(seq);
		return revLine;
	},
	compareToSameClass: function () {
		if (arguments.length === 1) {
			let o = arguments[0];
			var line = o;
			var i = 0;
			var j = 0;
			while (i < this.points.size() && j < line.points.size()) {
				var comparison = this.points.getCoordinate(i).compareTo(line.points.getCoordinate(j));
				if (comparison !== 0) {
					return comparison;
				}
				i++;
				j++;
			}
			if (i < this.points.size()) {
				return 1;
			}
			if (j < line.points.size()) {
				return -1;
			}
			return 0;
		} else if (arguments.length === 2) {
			let o = arguments[0], comp = arguments[1];
			var line = o;
			return comp.compare(this.points, line.points);
		}
	},
	apply: function () {
		if (hasInterface(arguments[0], CoordinateFilter)) {
			let filter = arguments[0];
			for (var i = 0; i < this.points.size(); i++) {
				filter.filter(this.points.getCoordinate(i));
			}
		} else if (hasInterface(arguments[0], CoordinateSequenceFilter)) {
			let filter = arguments[0];
			if (this.points.size() === 0) return null;
			for (var i = 0; i < this.points.size(); i++) {
				filter.filter(this.points, i);
				if (filter.isDone()) break;
			}
			if (filter.isGeometryChanged()) this.geometryChanged();
		} else if (hasInterface(arguments[0], GeometryFilter)) {
			let filter = arguments[0];
			filter.filter(this);
		} else if (hasInterface(arguments[0], GeometryComponentFilter)) {
			let filter = arguments[0];
			filter.filter(this);
		}
	},
	getBoundary: function () {
		return new BoundaryOp(this).getBoundary();
	},
	isEquivalentClass: function (other) {
		return other instanceof LineString;
	},
	clone: function () {
		var ls = Geometry.prototype.clone.call(this);
		ls.points = this.points.clone();
		return ls;
	},
	getCoordinateN: function (n) {
		return this.points.getCoordinate(n);
	},
	getGeometryType: function () {
		return "LineString";
	},
	copy: function () {
		return new LineString(this.points.copy(), this.factory);
	},
	getCoordinateSequence: function () {
		return this.points;
	},
	isEmpty: function () {
		return this.points.size() === 0;
	},
	init: function (points) {
		if (points === null) {
			points = this.getFactory().getCoordinateSequenceFactory().create([]);
		}
		if (points.size() === 1) {
			throw new IllegalArgumentException("Invalid number of points in LineString (found " + points.size() + " - must be 0 or >= 2)");
		}
		this.points = points;
	},
	isCoordinate: function (pt) {
		for (var i = 0; i < this.points.size(); i++) {
			if (this.points.getCoordinate(i).equals(pt)) {
				return true;
			}
		}
		return false;
	},
	getStartPoint: function () {
		if (this.isEmpty()) {
			return null;
		}
		return this.getPointN(0);
	},
	getPointN: function (n) {
		return this.getFactory().createPoint(this.points.getCoordinate(n));
	},
	interfaces_: function () {
		return [Lineal];
	},
	getClass: function () {
		return LineString;
	}
});
LineString.serialVersionUID = 3110669828065365560;

function Puntal() {}
extend$1(Puntal.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Puntal;
	}
});

function Point() {
	this.coordinates = null;
	let coordinates = arguments[0], factory = arguments[1];
	Geometry.call(this, factory);
	this.init(coordinates);
}
inherits(Point, Geometry);
extend$1(Point.prototype, {
	computeEnvelopeInternal: function () {
		if (this.isEmpty()) {
			return new Envelope();
		}
		var env = new Envelope();
		env.expandToInclude(this.coordinates.getX(0), this.coordinates.getY(0));
		return env;
	},
	getSortIndex: function () {
		return Geometry.SORTINDEX_POINT;
	},
	getCoordinates: function () {
		return this.isEmpty() ? [] : [this.getCoordinate()];
	},
	equalsExact: function () {
		if (arguments.length === 2) {
			let other = arguments[0], tolerance = arguments[1];
			if (!this.isEquivalentClass(other)) {
				return false;
			}
			if (this.isEmpty() && other.isEmpty()) {
				return true;
			}
			if (this.isEmpty() !== other.isEmpty()) {
				return false;
			}
			return this.equal(other.getCoordinate(), this.getCoordinate(), tolerance);
		} else return Geometry.prototype.equalsExact.apply(this, arguments);
	},
	normalize: function () {},
	getCoordinate: function () {
		return this.coordinates.size() !== 0 ? this.coordinates.getCoordinate(0) : null;
	},
	getBoundaryDimension: function () {
		return Dimension.FALSE;
	},
	getDimension: function () {
		return 0;
	},
	getNumPoints: function () {
		return this.isEmpty() ? 0 : 1;
	},
	reverse: function () {
		return this.copy();
	},
	getX: function () {
		if (this.getCoordinate() === null) {
			throw new IllegalStateException("getX called on empty Point");
		}
		return this.getCoordinate().x;
	},
	compareToSameClass: function () {
		if (arguments.length === 1) {
			let other = arguments[0];
			var point = other;
			return this.getCoordinate().compareTo(point.getCoordinate());
		} else if (arguments.length === 2) {
			let other = arguments[0], comp = arguments[1];
			var point = other;
			return comp.compare(this.coordinates, point.coordinates);
		}
	},
	apply: function () {
		if (hasInterface(arguments[0], CoordinateFilter)) {
			let filter = arguments[0];
			if (this.isEmpty()) {
				return null;
			}
			filter.filter(this.getCoordinate());
		} else if (hasInterface(arguments[0], CoordinateSequenceFilter)) {
			let filter = arguments[0];
			if (this.isEmpty()) return null;
			filter.filter(this.coordinates, 0);
			if (filter.isGeometryChanged()) this.geometryChanged();
		} else if (hasInterface(arguments[0], GeometryFilter)) {
			let filter = arguments[0];
			filter.filter(this);
		} else if (hasInterface(arguments[0], GeometryComponentFilter)) {
			let filter = arguments[0];
			filter.filter(this);
		}
	},
	getBoundary: function () {
		return this.getFactory().createGeometryCollection(null);
	},
	clone: function () {
		var p = Geometry.prototype.clone.call(this);
		p.coordinates = this.coordinates.clone();
		return p;
	},
	getGeometryType: function () {
		return "Point";
	},
	copy: function () {
		return new Point(this.coordinates.copy(), this.factory);
	},
	getCoordinateSequence: function () {
		return this.coordinates;
	},
	getY: function () {
		if (this.getCoordinate() === null) {
			throw new IllegalStateException("getY called on empty Point");
		}
		return this.getCoordinate().y;
	},
	isEmpty: function () {
		return this.coordinates.size() === 0;
	},
	init: function (coordinates) {
		if (coordinates === null) {
			coordinates = this.getFactory().getCoordinateSequenceFactory().create([]);
		}
		Assert.isTrue(coordinates.size() <= 1);
		this.coordinates = coordinates;
	},
	isSimple: function () {
		return true;
	},
	interfaces_: function () {
		return [Puntal];
	},
	getClass: function () {
		return Point;
	}
});
Point.serialVersionUID = 4902022702746614570;

function Polygonal() {}
extend$1(Polygonal.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Polygonal;
	}
});

function Polygon() {
	this.shell = null;
	this.holes = null;
	let shell = arguments[0], holes = arguments[1], factory = arguments[2];
	Geometry.call(this, factory);
	if (shell === null) {
		shell = this.getFactory().createLinearRing();
	}
	if (holes === null) {
		holes = [];
	}
	if (Geometry.hasNullElements(holes)) {
		throw new IllegalArgumentException("holes must not contain null elements");
	}
	if (shell.isEmpty() && Geometry.hasNonEmptyElements(holes)) {
		throw new IllegalArgumentException("shell is empty but holes are not");
	}
	this.shell = shell;
	this.holes = holes;
}
inherits(Polygon, Geometry);
extend$1(Polygon.prototype, {
	computeEnvelopeInternal: function () {
		return this.shell.getEnvelopeInternal();
	},
	getSortIndex: function () {
		return Geometry.SORTINDEX_POLYGON;
	},
	getCoordinates: function () {
		if (this.isEmpty()) {
			return [];
		}
		var coordinates = new Array(this.getNumPoints()).fill(null);
		var k = -1;
		var shellCoordinates = this.shell.getCoordinates();
		for (var x = 0; x < shellCoordinates.length; x++) {
			k++;
			coordinates[k] = shellCoordinates[x];
		}
		for (var i = 0; i < this.holes.length; i++) {
			var childCoordinates = this.holes[i].getCoordinates();
			for (var j = 0; j < childCoordinates.length; j++) {
				k++;
				coordinates[k] = childCoordinates[j];
			}
		}
		return coordinates;
	},
	getArea: function () {
		var area = 0.0;
		area += Math.abs(CGAlgorithms.signedArea(this.shell.getCoordinateSequence()));
		for (var i = 0; i < this.holes.length; i++) {
			area -= Math.abs(CGAlgorithms.signedArea(this.holes[i].getCoordinateSequence()));
		}
		return area;
	},
	isRectangle: function () {
		if (this.getNumInteriorRing() !== 0) return false;
		if (this.shell === null) return false;
		if (this.shell.getNumPoints() !== 5) return false;
		var seq = this.shell.getCoordinateSequence();
		var env = this.getEnvelopeInternal();
		for (var i = 0; i < 5; i++) {
			var x = seq.getX(i);
			if (!(x === env.getMinX() || x === env.getMaxX())) return false;
			var y = seq.getY(i);
			if (!(y === env.getMinY() || y === env.getMaxY())) return false;
		}
		var prevX = seq.getX(0);
		var prevY = seq.getY(0);
		for (var i = 1; i <= 4; i++) {
			var x = seq.getX(i);
			var y = seq.getY(i);
			var xChanged = x !== prevX;
			var yChanged = y !== prevY;
			if (xChanged === yChanged) return false;
			prevX = x;
			prevY = y;
		}
		return true;
	},
	equalsExact: function () {
		if (arguments.length === 2) {
			let other = arguments[0], tolerance = arguments[1];
			if (!this.isEquivalentClass(other)) {
				return false;
			}
			var otherPolygon = other;
			var thisShell = this.shell;
			var otherPolygonShell = otherPolygon.shell;
			if (!thisShell.equalsExact(otherPolygonShell, tolerance)) {
				return false;
			}
			if (this.holes.length !== otherPolygon.holes.length) {
				return false;
			}
			for (var i = 0; i < this.holes.length; i++) {
				if (!this.holes[i].equalsExact(otherPolygon.holes[i], tolerance)) {
					return false;
				}
			}
			return true;
		} else return Geometry.prototype.equalsExact.apply(this, arguments);
	},
	normalize: function () {
		if (arguments.length === 0) {
			this.normalize(this.shell, true);
			for (var i = 0; i < this.holes.length; i++) {
				this.normalize(this.holes[i], false);
			}
			Arrays.sort(this.holes);
		} else if (arguments.length === 2) {
			let ring = arguments[0], clockwise = arguments[1];
			if (ring.isEmpty()) {
				return null;
			}
			var uniqueCoordinates = new Array(ring.getCoordinates().length - 1).fill(null);
			System.arraycopy(ring.getCoordinates(), 0, uniqueCoordinates, 0, uniqueCoordinates.length);
			var minCoordinate = CoordinateArrays.minCoordinate(ring.getCoordinates());
			CoordinateArrays.scroll(uniqueCoordinates, minCoordinate);
			System.arraycopy(uniqueCoordinates, 0, ring.getCoordinates(), 0, uniqueCoordinates.length);
			ring.getCoordinates()[uniqueCoordinates.length] = uniqueCoordinates[0];
			if (CGAlgorithms.isCCW(ring.getCoordinates()) === clockwise) {
				CoordinateArrays.reverse(ring.getCoordinates());
			}
		}
	},
	getCoordinate: function () {
		return this.shell.getCoordinate();
	},
	getNumInteriorRing: function () {
		return this.holes.length;
	},
	getBoundaryDimension: function () {
		return 1;
	},
	getDimension: function () {
		return 2;
	},
	getLength: function () {
		var len = 0.0;
		len += this.shell.getLength();
		for (var i = 0; i < this.holes.length; i++) {
			len += this.holes[i].getLength();
		}
		return len;
	},
	getNumPoints: function () {
		var numPoints = this.shell.getNumPoints();
		for (var i = 0; i < this.holes.length; i++) {
			numPoints += this.holes[i].getNumPoints();
		}
		return numPoints;
	},
	reverse: function () {
		var poly = this.copy();
		poly.shell = this.shell.copy().reverse();
		poly.holes = new Array(this.holes.length).fill(null);
		for (var i = 0; i < this.holes.length; i++) {
			poly.holes[i] = this.holes[i].copy().reverse();
		}
		return poly;
	},
	convexHull: function () {
		return this.getExteriorRing().convexHull();
	},
	compareToSameClass: function () {
		if (arguments.length === 1) {
			let o = arguments[0];
			var thisShell = this.shell;
			var otherShell = o.shell;
			return thisShell.compareToSameClass(otherShell);
		} else if (arguments.length === 2) {
			let o = arguments[0], comp = arguments[1];
			var poly = o;
			var thisShell = this.shell;
			var otherShell = poly.shell;
			var shellComp = thisShell.compareToSameClass(otherShell, comp);
			if (shellComp !== 0) return shellComp;
			var nHole1 = this.getNumInteriorRing();
			var nHole2 = poly.getNumInteriorRing();
			var i = 0;
			while (i < nHole1 && i < nHole2) {
				var thisHole = this.getInteriorRingN(i);
				var otherHole = poly.getInteriorRingN(i);
				var holeComp = thisHole.compareToSameClass(otherHole, comp);
				if (holeComp !== 0) return holeComp;
				i++;
			}
			if (i < nHole1) return 1;
			if (i < nHole2) return -1;
			return 0;
		}
	},
	apply: function () {
		if (hasInterface(arguments[0], CoordinateFilter)) {
			let filter = arguments[0];
			this.shell.apply(filter);
			for (var i = 0; i < this.holes.length; i++) {
				this.holes[i].apply(filter);
			}
		} else if (hasInterface(arguments[0], CoordinateSequenceFilter)) {
			let filter = arguments[0];
			this.shell.apply(filter);
			if (!filter.isDone()) {
				for (var i = 0; i < this.holes.length; i++) {
					this.holes[i].apply(filter);
					if (filter.isDone()) break;
				}
			}
			if (filter.isGeometryChanged()) this.geometryChanged();
		} else if (hasInterface(arguments[0], GeometryFilter)) {
			let filter = arguments[0];
			filter.filter(this);
		} else if (hasInterface(arguments[0], GeometryComponentFilter)) {
			let filter = arguments[0];
			filter.filter(this);
			this.shell.apply(filter);
			for (var i = 0; i < this.holes.length; i++) {
				this.holes[i].apply(filter);
			}
		}
	},
	getBoundary: function () {
		if (this.isEmpty()) {
			return this.getFactory().createMultiLineString();
		}
		var rings = new Array(this.holes.length + 1).fill(null);
		rings[0] = this.shell;
		for (var i = 0; i < this.holes.length; i++) {
			rings[i + 1] = this.holes[i];
		}
		if (rings.length <= 1) return this.getFactory().createLinearRing(rings[0].getCoordinateSequence());
		return this.getFactory().createMultiLineString(rings);
	},
	clone: function () {
		var poly = Geometry.prototype.clone.call(this);
		poly.shell = this.shell.clone();
		poly.holes = new Array(this.holes.length).fill(null);
		for (var i = 0; i < this.holes.length; i++) {
			poly.holes[i] = this.holes[i].clone();
		}
		return poly;
	},
	getGeometryType: function () {
		return "Polygon";
	},
	copy: function () {
		var shell = this.shell.copy();
		var holes = new Array(this.holes.length).fill(null);
		for (var i = 0; i < holes.length; i++) {
			holes[i] = this.holes[i].copy();
		}
		return new Polygon(shell, holes, this.factory);
	},
	getExteriorRing: function () {
		return this.shell;
	},
	isEmpty: function () {
		return this.shell.isEmpty();
	},
	getInteriorRingN: function (n) {
		return this.holes[n];
	},
	interfaces_: function () {
		return [Polygonal];
	},
	getClass: function () {
		return Polygon;
	}
});
Polygon.serialVersionUID = -3494792200821764533;

function MultiPoint() {
	let points = arguments[0], factory = arguments[1];
	GeometryCollection.call(this, points, factory);
}
inherits(MultiPoint, GeometryCollection);
extend$1(MultiPoint.prototype, {
	getSortIndex: function () {
		return Geometry.SORTINDEX_MULTIPOINT;
	},
	isValid: function () {
		return true;
	},
	equalsExact: function () {
		if (arguments.length === 2) {
			let other = arguments[0], tolerance = arguments[1];
			if (!this.isEquivalentClass(other)) {
				return false;
			}
			return GeometryCollection.prototype.equalsExact.call(this, other, tolerance);
		} else return GeometryCollection.prototype.equalsExact.apply(this, arguments);
	},
	getCoordinate: function () {
		if (arguments.length === 1) {
			let n = arguments[0];
			return this.geometries[n].getCoordinate();
		} else return GeometryCollection.prototype.getCoordinate.apply(this, arguments);
	},
	getBoundaryDimension: function () {
		return Dimension.FALSE;
	},
	getDimension: function () {
		return 0;
	},
	getBoundary: function () {
		return this.getFactory().createGeometryCollection(null);
	},
	getGeometryType: function () {
		return "MultiPoint";
	},
	copy: function () {
		var points = new Array(this.geometries.length).fill(null);
		for (var i = 0; i < points.length; i++) {
			points[i] = this.geometries[i].copy();
		}
		return new MultiPoint(points, this.factory);
	},
	interfaces_: function () {
		return [Puntal];
	},
	getClass: function () {
		return MultiPoint;
	}
});
MultiPoint.serialVersionUID = -8048474874175355449;

function LinearRing() {
	if (arguments[0] instanceof Coordinate && arguments[1] instanceof GeometryFactory) {
		let points = arguments[0], factory = arguments[1];
		LinearRing.call(this, factory.getCoordinateSequenceFactory().create(points), factory);
	} else if (hasInterface(arguments[0], CoordinateSequence) && arguments[1] instanceof GeometryFactory) {
		let points = arguments[0], factory = arguments[1];
		LineString.call(this, points, factory);
		this.validateConstruction();
	}
}
inherits(LinearRing, LineString);
extend$1(LinearRing.prototype, {
	getSortIndex: function () {
		return Geometry.SORTINDEX_LINEARRING;
	},
	getBoundaryDimension: function () {
		return Dimension.FALSE;
	},
	isClosed: function () {
		if (this.isEmpty()) {
			return true;
		}
		return LineString.prototype.isClosed.call(this);
	},
	reverse: function () {
		var seq = this.points.copy();
		CoordinateSequences.reverse(seq);
		var rev = this.getFactory().createLinearRing(seq);
		return rev;
	},
	validateConstruction: function () {
		if (!this.isEmpty() && !LineString.prototype.isClosed.call(this)) {
			throw new IllegalArgumentException("Points of LinearRing do not form a closed linestring");
		}
		if (this.getCoordinateSequence().size() >= 1 && this.getCoordinateSequence().size() < LinearRing.MINIMUM_VALID_SIZE) {
			throw new IllegalArgumentException("Invalid number of points in LinearRing (found " + this.getCoordinateSequence().size() + " - must be 0 or >= 4)");
		}
	},
	getGeometryType: function () {
		return "LinearRing";
	},
	copy: function () {
		return new LinearRing(this.points.copy(), this.factory);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return LinearRing;
	}
});
LinearRing.MINIMUM_VALID_SIZE = 4;
LinearRing.serialVersionUID = -4261142084085851829;

function MultiPolygon() {
	let polygons = arguments[0], factory = arguments[1];
	GeometryCollection.call(this, polygons, factory);
}
inherits(MultiPolygon, GeometryCollection);
extend$1(MultiPolygon.prototype, {
	getSortIndex: function () {
		return Geometry.SORTINDEX_MULTIPOLYGON;
	},
	equalsExact: function () {
		if (arguments.length === 2) {
			let other = arguments[0], tolerance = arguments[1];
			if (!this.isEquivalentClass(other)) {
				return false;
			}
			return GeometryCollection.prototype.equalsExact.call(this, other, tolerance);
		} else return GeometryCollection.prototype.equalsExact.apply(this, arguments);
	},
	getBoundaryDimension: function () {
		return 1;
	},
	getDimension: function () {
		return 2;
	},
	reverse: function () {
		var n = this.geometries.length;
		var revGeoms = new Array(n).fill(null);
		for (var i = 0; i < this.geometries.length; i++) {
			revGeoms[i] = this.geometries[i].reverse();
		}
		return this.getFactory().createMultiPolygon(revGeoms);
	},
	getBoundary: function () {
		if (this.isEmpty()) {
			return this.getFactory().createMultiLineString();
		}
		var allRings = new ArrayList();
		for (var i = 0; i < this.geometries.length; i++) {
			var polygon = this.geometries[i];
			var rings = polygon.getBoundary();
			for (var j = 0; j < rings.getNumGeometries(); j++) {
				allRings.add(rings.getGeometryN(j));
			}
		}
		var allRingsArray = new Array(allRings.size()).fill(null);
		return this.getFactory().createMultiLineString(allRings.toArray(allRingsArray));
	},
	getGeometryType: function () {
		return "MultiPolygon";
	},
	copy: function () {
		var polygons = new Array(this.geometries.length).fill(null);
		for (var i = 0; i < polygons.length; i++) {
			polygons[i] = this.geometries[i].copy();
		}
		return new MultiPolygon(polygons, this.factory);
	},
	interfaces_: function () {
		return [Polygonal];
	},
	getClass: function () {
		return MultiPolygon;
	}
});
MultiPolygon.serialVersionUID = -551033529766975875;

function GeometryEditor() {
	this.factory = null;
	this.isUserDataCopied = false;
	if (arguments.length === 0) {} else if (arguments.length === 1) {
		let factory = arguments[0];
		this.factory = factory;
	}
}
extend$1(GeometryEditor.prototype, {
	setCopyUserData: function (isUserDataCopied) {
		this.isUserDataCopied = isUserDataCopied;
	},
	edit: function (geometry, operation) {
		if (geometry === null) return null;
		var result = this.editInternal(geometry, operation);
		if (this.isUserDataCopied) {
			result.setUserData(geometry.getUserData());
		}
		return result;
	},
	editInternal: function (geometry, operation) {
		if (this.factory === null) this.factory = geometry.getFactory();
		if (geometry instanceof GeometryCollection) {
			return this.editGeometryCollection(geometry, operation);
		}
		if (geometry instanceof Polygon) {
			return this.editPolygon(geometry, operation);
		}
		if (geometry instanceof Point) {
			return operation.edit(geometry, this.factory);
		}
		if (geometry instanceof LineString) {
			return operation.edit(geometry, this.factory);
		}
		Assert.shouldNeverReachHere("Unsupported Geometry class: " + geometry.getClass().getName());
		return null;
	},
	editGeometryCollection: function (collection, operation) {
		var collectionForType = operation.edit(collection, this.factory);
		var geometries = new ArrayList();
		for (var i = 0; i < collectionForType.getNumGeometries(); i++) {
			var geometry = this.edit(collectionForType.getGeometryN(i), operation);
			if (geometry === null || geometry.isEmpty()) {
				continue;
			}
			geometries.add(geometry);
		}
		if (collectionForType.getClass() === MultiPoint) {
			return this.factory.createMultiPoint(geometries.toArray([]));
		}
		if (collectionForType.getClass() === MultiLineString) {
			return this.factory.createMultiLineString(geometries.toArray([]));
		}
		if (collectionForType.getClass() === MultiPolygon) {
			return this.factory.createMultiPolygon(geometries.toArray([]));
		}
		return this.factory.createGeometryCollection(geometries.toArray([]));
	},
	editPolygon: function (polygon, operation) {
		var newPolygon = operation.edit(polygon, this.factory);
		if (newPolygon === null) newPolygon = this.factory.createPolygon(null);
		if (newPolygon.isEmpty()) {
			return newPolygon;
		}
		var shell = this.edit(newPolygon.getExteriorRing(), operation);
		if (shell === null || shell.isEmpty()) {
			return this.factory.createPolygon();
		}
		var holes = new ArrayList();
		for (var i = 0; i < newPolygon.getNumInteriorRing(); i++) {
			var hole = this.edit(newPolygon.getInteriorRingN(i), operation);
			if (hole === null || hole.isEmpty()) {
				continue;
			}
			holes.add(hole);
		}
		return this.factory.createPolygon(shell, holes.toArray([]));
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return GeometryEditor;
	}
});
function GeometryEditorOperation() {}
GeometryEditor.GeometryEditorOperation = GeometryEditorOperation;
function NoOpGeometryOperation() {}
extend$1(NoOpGeometryOperation.prototype, {
	edit: function (geometry, factory) {
		return geometry;
	},
	interfaces_: function () {
		return [GeometryEditorOperation];
	},
	getClass: function () {
		return NoOpGeometryOperation;
	}
});
function CoordinateOperation() {}
extend$1(CoordinateOperation.prototype, {
	edit: function (geometry, factory) {
		var coords = this.editCoordinates(geometry.getCoordinates(), geometry);
		if (coords === null) return geometry;
		if (geometry instanceof LinearRing) {
			return factory.createLinearRing(coords);
		}
		if (geometry instanceof LineString) {
			return factory.createLineString(coords);
		}
		if (geometry instanceof Point) {
			if (coords.length > 0) {
				return factory.createPoint(coords[0]);
			} else {
				return factory.createPoint();
			}
		}
		return geometry;
	},
	interfaces_: function () {
		return [GeometryEditorOperation];
	},
	getClass: function () {
		return CoordinateOperation;
	}
});
function CoordinateSequenceOperation() {}
extend$1(CoordinateSequenceOperation.prototype, {
	edit: function (geometry, factory) {
		if (geometry instanceof LinearRing) {
			return factory.createLinearRing(this.edit(geometry.getCoordinateSequence(), geometry));
		}
		if (geometry instanceof LineString) {
			return factory.createLineString(this.edit(geometry.getCoordinateSequence(), geometry));
		}
		if (geometry instanceof Point) {
			return factory.createPoint(this.edit(geometry.getCoordinateSequence(), geometry));
		}
		return geometry;
	},
	interfaces_: function () {
		return [GeometryEditorOperation];
	},
	getClass: function () {
		return CoordinateSequenceOperation;
	}
});
GeometryEditor.NoOpGeometryOperation = NoOpGeometryOperation;
GeometryEditor.CoordinateOperation = CoordinateOperation;
GeometryEditor.CoordinateSequenceOperation = CoordinateSequenceOperation;

function CoordinateArraySequence() {
	this.dimension = 3;
	this.coordinates = null;
	if (arguments.length === 1) {
		if (arguments[0] instanceof Array) {
			let coordinates = arguments[0];
			CoordinateArraySequence.call(this, coordinates, 3);
		} else if (Number.isInteger(arguments[0])) {
			let size = arguments[0];
			this.coordinates = new Array(size).fill(null);
			for (var i = 0; i < size; i++) {
				this.coordinates[i] = new Coordinate();
			}
		} else if (hasInterface(arguments[0], CoordinateSequence)) {
			let coordSeq = arguments[0];
			if (coordSeq === null) {
				this.coordinates = new Array(0).fill(null);
				return null;
			}
			this.dimension = coordSeq.getDimension();
			this.coordinates = new Array(coordSeq.size()).fill(null);
			for (var i = 0; i < this.coordinates.length; i++) {
				this.coordinates[i] = coordSeq.getCoordinateCopy(i);
			}
		}
	} else if (arguments.length === 2) {
		if (arguments[0] instanceof Array && Number.isInteger(arguments[1])) {
			let coordinates = arguments[0], dimension = arguments[1];
			this.coordinates = coordinates;
			this.dimension = dimension;
			if (coordinates === null) this.coordinates = new Array(0).fill(null);
		} else if (Number.isInteger(arguments[0]) && Number.isInteger(arguments[1])) {
			let size = arguments[0], dimension = arguments[1];
			this.coordinates = new Array(size).fill(null);
			this.dimension = dimension;
			for (var i = 0; i < size; i++) {
				this.coordinates[i] = new Coordinate();
			}
		}
	}
}
extend$1(CoordinateArraySequence.prototype, {
	setOrdinate: function (index, ordinateIndex, value) {
		switch (ordinateIndex) {
			case CoordinateSequence.X:
				this.coordinates[index].x = value;
				break;
			case CoordinateSequence.Y:
				this.coordinates[index].y = value;
				break;
			case CoordinateSequence.Z:
				this.coordinates[index].z = value;
				break;
			default:
				throw new IllegalArgumentException("invalid ordinateIndex");
		}
	},
	size: function () {
		return this.coordinates.length;
	},
	getOrdinate: function (index, ordinateIndex) {
		switch (ordinateIndex) {
			case CoordinateSequence.X:
				return this.coordinates[index].x;
			case CoordinateSequence.Y:
				return this.coordinates[index].y;
			case CoordinateSequence.Z:
				return this.coordinates[index].z;
		}
		return Double.NaN;
	},
	getCoordinate: function () {
		if (arguments.length === 1) {
			let i = arguments[0];
			return this.coordinates[i];
		} else if (arguments.length === 2) {
			let index = arguments[0], coord = arguments[1];
			coord.x = this.coordinates[index].x;
			coord.y = this.coordinates[index].y;
			coord.z = this.coordinates[index].z;
		}
	},
	getCoordinateCopy: function (i) {
		return new Coordinate(this.coordinates[i]);
	},
	getDimension: function () {
		return this.dimension;
	},
	getX: function (index) {
		return this.coordinates[index].x;
	},
	clone: function () {
		var cloneCoordinates = new Array(this.size()).fill(null);
		for (var i = 0; i < this.coordinates.length; i++) {
			cloneCoordinates[i] = this.coordinates[i].clone();
		}
		return new CoordinateArraySequence(cloneCoordinates, this.dimension);
	},
	expandEnvelope: function (env) {
		for (var i = 0; i < this.coordinates.length; i++) {
			env.expandToInclude(this.coordinates[i]);
		}
		return env;
	},
	copy: function () {
		var cloneCoordinates = new Array(this.size()).fill(null);
		for (var i = 0; i < this.coordinates.length; i++) {
			cloneCoordinates[i] = this.coordinates[i].copy();
		}
		return new CoordinateArraySequence(cloneCoordinates, this.dimension);
	},
	toString: function () {
		if (this.coordinates.length > 0) {
			var strBuf = new StringBuffer(17 * this.coordinates.length);
			strBuf.append('(');
			strBuf.append(this.coordinates[0]);
			for (var i = 1; i < this.coordinates.length; i++) {
				strBuf.append(", ");
				strBuf.append(this.coordinates[i]);
			}
			strBuf.append(')');
			return strBuf.toString();
		} else {
			return "()";
		}
	},
	getY: function (index) {
		return this.coordinates[index].y;
	},
	toCoordinateArray: function () {
		return this.coordinates;
	},
	interfaces_: function () {
		return [CoordinateSequence, Serializable];
	},
	getClass: function () {
		return CoordinateArraySequence;
	}
});
CoordinateArraySequence.serialVersionUID = -915438501601840650;

function CoordinateArraySequenceFactory() {}
extend$1(CoordinateArraySequenceFactory.prototype, {
	readResolve: function () {
		return CoordinateArraySequenceFactory.instance();
	},
	create: function () {
		if (arguments.length === 1) {
			if (arguments[0] instanceof Array) {
				let coordinates = arguments[0];
				return new CoordinateArraySequence(coordinates);
			} else if (hasInterface(arguments[0], CoordinateSequence)) {
				let coordSeq = arguments[0];
				return new CoordinateArraySequence(coordSeq);
			}
		} else if (arguments.length === 2) {
			let size = arguments[0], dimension = arguments[1];
			if (dimension > 3) dimension = 3;
			if (dimension < 2) return new CoordinateArraySequence(size);
			return new CoordinateArraySequence(size, dimension);
		}
	},
	interfaces_: function () {
		return [CoordinateSequenceFactory, Serializable];
	},
	getClass: function () {
		return CoordinateArraySequenceFactory;
	}
});
CoordinateArraySequenceFactory.instance = function () {
	return CoordinateArraySequenceFactory.instanceObject;
};
CoordinateArraySequenceFactory.serialVersionUID = -4099577099607551657;
CoordinateArraySequenceFactory.instanceObject = new CoordinateArraySequenceFactory();

// shared pointer
var i;
// shortcuts
var defineProperty = Object.defineProperty;
function is (a, b) { return (a === b) || (a !== a && b !== b) } // eslint-disable-line

var MapPolyfill = createCollection({
  // WeakMap#delete(key:void*):boolean
  'delete': sharedDelete,
  // :was Map#get(key:void*[, d3fault:void*]):void*
  // Map#has(key:void*):boolean
  has: mapHas,
  // Map#get(key:void*):boolean
  get: sharedGet,
  // Map#set(key:void*, value:void*):void
  set: sharedSet,
  // Map#keys(void):Iterator
  keys: sharedKeys,
  // Map#values(void):Iterator
  values: sharedValues,
  // Map#entries(void):Iterator
  entries: mapEntries,
  // Map#forEach(callback:Function, context:void*):void ==> callback.call(context, key, value, mapObject) === not in specs`
  forEach: sharedForEach,
  // Map#clear():
  clear: sharedClear
});

/**
 * ES6 collection constructor
 * @return {Function} a collection class
 */
function createCollection (proto, objectOnly) {
  function Collection (a) {
    if (!this || this.constructor !== Collection) return new Collection(a)
    this._keys = [];
    this._values = [];
    this._itp = []; // iteration pointers
    this.objectOnly = objectOnly;

    // parse initial iterable argument passed
    if (a) init.call(this, a);
  }

  // define size for non object-only collections
  if (!objectOnly) {
    defineProperty(proto, 'size', {
      get: sharedSize
    });
  }

  // set prototype
  proto.constructor = Collection;
  Collection.prototype = proto;

  return Collection
}

/** parse initial iterable argument passed */
function init (a) {
  // init Set argument, like `[1,2,3,{}]`
  if (this.add) a.forEach(this.add, this);
  // init Map argument like `[[1,2], [{}, 4]]`
  else a.forEach(function (a) { this.set(a[0], a[1]); }, this);
}

/** delete */
function sharedDelete (key) {
  if (this.has(key)) {
    this._keys.splice(i, 1);
    this._values.splice(i, 1);
    // update iteration pointers
    this._itp.forEach(function (p) { if (i < p[0]) p[0]--; });
  }
  // Aurora here does it while Canary doesn't
  return i > -1
}

function sharedGet (key) {
  return this.has(key) ? this._values[i] : undefined
}

function has (list, key) {
  if (this.objectOnly && key !== Object(key)) throw new TypeError('Invalid value used as weak collection key')
  // NaN or 0 passed
  if (key !== key || key === 0) for (i = list.length; i-- && !is(list[i], key);) {} // eslint-disable-line
  else i = list.indexOf(key);
  return i > -1
}

function mapHas (value) {
  return has.call(this, this._keys, value)
}

/** @chainable */
function sharedSet (key, value) {
  this.has(key) ? this._values[i] = value : this._values[this._keys.push(key) - 1] = value;
  return this
}

function sharedClear () {
  (this._keys || 0).length =
    this._values.length = 0;
}

/** keys, values, and iterate related methods */
function sharedKeys () {
  return sharedIterator(this._itp, this._keys)
}

function sharedValues () {
  return sharedIterator(this._itp, this._values)
}

function mapEntries () {
  return sharedIterator(this._itp, this._keys, this._values)
}

function sharedIterator (itp, array, array2) {
  var p = [0];
  var done = false;
  itp.push(p);
  return {
    next: function () {
      var v;
      var k = p[0];
      if (!done && k < array.length) {
        v = array2 ? [array[k], array2[k]] : array[k];
        p[0]++;
      } else {
        done = true;
        itp.splice(itp.indexOf(p), 1);
      }
      return { done: done, value: v }
    }
  }
}

function sharedSize () {
  return this._values.length
}

function sharedForEach (callback, context) {
  var it = this.entries();
  for (;;) {
    var r = it.next();
    if (r.done) break
    callback.call(context, r.value[1], r.value[0], this);
  }
}

let MapImpl = typeof Map === 'undefined' || !Map.prototype.values ? MapPolyfill : Map;

/**
 * @see http://download.oracle.com/javase/6/docs/api/java/util/HashMap.html
 *
 * @extends {javascript.util.Map}
 * @constructor
 * @private
 */
function HashMap () {
  /**
   * @type {Object}
   * @private
  */
  this.map_ = new MapImpl();
}
HashMap.prototype = new Map$1();

/**
 * @override
 */
HashMap.prototype.get = function (key) {
  return this.map_.get(key) || null
};

/**
 * @override
 */
HashMap.prototype.put = function (key, value) {
  this.map_.set(key, value);
  return value
};

/**
 * @override
 */
HashMap.prototype.values = function () {
  const arrayList = new ArrayList();
  const it = this.map_.values();
  let o = it.next();
  while (!o.done) {
    arrayList.add(o.value);
    o = it.next();
  }
  return arrayList
};

/**
 * @override
 */
HashMap.prototype.entrySet = function () {
  const hashSet = new HashSet();
  this.map_.entries().forEach(entry => hashSet.add(entry));
  return hashSet
};

/**
 * @override
 */
HashMap.prototype.size = function () {
  return this.map_.size()
};

function PrecisionModel() {
	this.modelType = null;
	this.scale = null;
	if (arguments.length === 0) {
		this.modelType = PrecisionModel.FLOATING;
	} else if (arguments.length === 1) {
		if (arguments[0] instanceof Type) {
			let modelType = arguments[0];
			this.modelType = modelType;
			if (modelType === PrecisionModel.FIXED) {
				this.setScale(1.0);
			}
		} else if (typeof arguments[0] === "number") {
			let scale = arguments[0];
			this.modelType = PrecisionModel.FIXED;
			this.setScale(scale);
		} else if (arguments[0] instanceof PrecisionModel) {
			let pm = arguments[0];
			this.modelType = pm.modelType;
			this.scale = pm.scale;
		}
	}
}
extend$1(PrecisionModel.prototype, {
	equals: function (other) {
		if (!(other instanceof PrecisionModel)) {
			return false;
		}
		var otherPrecisionModel = other;
		return this.modelType === otherPrecisionModel.modelType && this.scale === otherPrecisionModel.scale;
	},
	compareTo: function (o) {
		var other = o;
		var sigDigits = this.getMaximumSignificantDigits();
		var otherSigDigits = other.getMaximumSignificantDigits();
		return new Integer(sigDigits).compareTo(new Integer(otherSigDigits));
	},
	getScale: function () {
		return this.scale;
	},
	isFloating: function () {
		return this.modelType === PrecisionModel.FLOATING || this.modelType === PrecisionModel.FLOATING_SINGLE;
	},
	getType: function () {
		return this.modelType;
	},
	toString: function () {
		var description = "UNKNOWN";
		if (this.modelType === PrecisionModel.FLOATING) {
			description = "Floating";
		} else if (this.modelType === PrecisionModel.FLOATING_SINGLE) {
			description = "Floating-Single";
		} else if (this.modelType === PrecisionModel.FIXED) {
			description = "Fixed (Scale=" + this.getScale() + ")";
		}
		return description;
	},
	makePrecise: function () {
		if (typeof arguments[0] === "number") {
			let val = arguments[0];
			if (Double.isNaN(val)) return val;
			if (this.modelType === PrecisionModel.FLOATING_SINGLE) {
				var floatSingleVal = val;
				return floatSingleVal;
			}
			if (this.modelType === PrecisionModel.FIXED) {
				return Math.round(val * this.scale) / this.scale;
			}
			return val;
		} else if (arguments[0] instanceof Coordinate) {
			let coord = arguments[0];
			if (this.modelType === PrecisionModel.FLOATING) return null;
			coord.x = this.makePrecise(coord.x);
			coord.y = this.makePrecise(coord.y);
		}
	},
	getMaximumSignificantDigits: function () {
		var maxSigDigits = 16;
		if (this.modelType === PrecisionModel.FLOATING) {
			maxSigDigits = 16;
		} else if (this.modelType === PrecisionModel.FLOATING_SINGLE) {
			maxSigDigits = 6;
		} else if (this.modelType === PrecisionModel.FIXED) {
			maxSigDigits = 1 + Math.trunc(Math.ceil(Math.log(this.getScale()) / Math.log(10)));
		}
		return maxSigDigits;
	},
	setScale: function (scale) {
		this.scale = Math.abs(scale);
	},
	interfaces_: function () {
		return [Serializable, Comparable];
	},
	getClass: function () {
		return PrecisionModel;
	}
});
PrecisionModel.mostPrecise = function (pm1, pm2) {
	if (pm1.compareTo(pm2) >= 0) return pm1;
	return pm2;
};
function Type() {
	this.name = null;
	let name = arguments[0];
	this.name = name;
	Type.nameToTypeMap.put(name, this);
}
extend$1(Type.prototype, {
	readResolve: function () {
		return Type.nameToTypeMap.get(this.name);
	},
	toString: function () {
		return this.name;
	},
	interfaces_: function () {
		return [Serializable];
	},
	getClass: function () {
		return Type;
	}
});
Type.serialVersionUID = -5528602631731589822;
Type.nameToTypeMap = new HashMap();
PrecisionModel.Type = Type;
PrecisionModel.serialVersionUID = 7777263578777803835;
PrecisionModel.FIXED = new Type("FIXED");
PrecisionModel.FLOATING = new Type("FLOATING");
PrecisionModel.FLOATING_SINGLE = new Type("FLOATING SINGLE");
PrecisionModel.maximumPreciseValue = 9007199254740992.0;

function GeometryFactory() {
	this.precisionModel = null;
	this.coordinateSequenceFactory = null;
	this.SRID = null;
	if (arguments.length === 0) {
		GeometryFactory.call(this, new PrecisionModel(), 0);
	} else if (arguments.length === 1) {
		if (hasInterface(arguments[0], CoordinateSequenceFactory)) {
			let coordinateSequenceFactory = arguments[0];
			GeometryFactory.call(this, new PrecisionModel(), 0, coordinateSequenceFactory);
		} else if (arguments[0] instanceof PrecisionModel) {
			let precisionModel = arguments[0];
			GeometryFactory.call(this, precisionModel, 0, GeometryFactory.getDefaultCoordinateSequenceFactory());
		}
	} else if (arguments.length === 2) {
		let precisionModel = arguments[0], SRID = arguments[1];
		GeometryFactory.call(this, precisionModel, SRID, GeometryFactory.getDefaultCoordinateSequenceFactory());
	} else if (arguments.length === 3) {
		let precisionModel = arguments[0], SRID = arguments[1], coordinateSequenceFactory = arguments[2];
		this.precisionModel = precisionModel;
		this.coordinateSequenceFactory = coordinateSequenceFactory;
		this.SRID = SRID;
	}
}
extend$1(GeometryFactory.prototype, {
	toGeometry: function (envelope) {
		if (envelope.isNull()) {
			return this.createPoint(null);
		}
		if (envelope.getMinX() === envelope.getMaxX() && envelope.getMinY() === envelope.getMaxY()) {
			return this.createPoint(new Coordinate(envelope.getMinX(), envelope.getMinY()));
		}
		if (envelope.getMinX() === envelope.getMaxX() || envelope.getMinY() === envelope.getMaxY()) {
			return this.createLineString([new Coordinate(envelope.getMinX(), envelope.getMinY()), new Coordinate(envelope.getMaxX(), envelope.getMaxY())]);
		}
		return this.createPolygon(this.createLinearRing([new Coordinate(envelope.getMinX(), envelope.getMinY()), new Coordinate(envelope.getMinX(), envelope.getMaxY()), new Coordinate(envelope.getMaxX(), envelope.getMaxY()), new Coordinate(envelope.getMaxX(), envelope.getMinY()), new Coordinate(envelope.getMinX(), envelope.getMinY())]), null);
	},
	createLineString: function () {
		if (arguments.length === 0) {
			return this.createLineString(this.getCoordinateSequenceFactory().create([]));
		} else if (arguments.length === 1) {
			if (arguments[0] instanceof Array) {
				let coordinates = arguments[0];
				return this.createLineString(coordinates !== null ? this.getCoordinateSequenceFactory().create(coordinates) : null);
			} else if (hasInterface(arguments[0], CoordinateSequence)) {
				let coordinates = arguments[0];
				return new LineString(coordinates, this);
			}
		}
	},
	createMultiLineString: function () {
		if (arguments.length === 0) {
			return new MultiLineString(null, this);
		} else if (arguments.length === 1) {
			let lineStrings = arguments[0];
			return new MultiLineString(lineStrings, this);
		}
	},
	buildGeometry: function (geomList) {
		var geomClass = null;
		var isHeterogeneous = false;
		var hasGeometryCollection = false;
		for (var i = geomList.iterator(); i.hasNext(); ) {
			var geom = i.next();
			var partClass = geom.getClass();
			if (geomClass === null) {
				geomClass = partClass;
			}
			if (partClass !== geomClass) {
				isHeterogeneous = true;
			}
			if (geom.isGeometryCollectionOrDerived()) hasGeometryCollection = true;
		}
		if (geomClass === null) {
			return this.createGeometryCollection();
		}
		if (isHeterogeneous || hasGeometryCollection) {
			return this.createGeometryCollection(GeometryFactory.toGeometryArray(geomList));
		}
		var geom0 = geomList.iterator().next();
		var isCollection = geomList.size() > 1;
		if (isCollection) {
			if (geom0 instanceof Polygon) {
				return this.createMultiPolygon(GeometryFactory.toPolygonArray(geomList));
			} else if (geom0 instanceof LineString) {
				return this.createMultiLineString(GeometryFactory.toLineStringArray(geomList));
			} else if (geom0 instanceof Point) {
				return this.createMultiPoint(GeometryFactory.toPointArray(geomList));
			}
			Assert.shouldNeverReachHere("Unhandled class: " + geom0.getClass().getName());
		}
		return geom0;
	},
	createMultiPointFromCoords: function (coordinates) {
		return this.createMultiPoint(coordinates !== null ? this.getCoordinateSequenceFactory().create(coordinates) : null);
	},
	createPoint: function () {
		if (arguments.length === 0) {
			return this.createPoint(this.getCoordinateSequenceFactory().create([]));
		} else if (arguments.length === 1) {
			if (arguments[0] instanceof Coordinate) {
				let coordinate = arguments[0];
				return this.createPoint(coordinate !== null ? this.getCoordinateSequenceFactory().create([coordinate]) : null);
			} else if (hasInterface(arguments[0], CoordinateSequence)) {
				let coordinates = arguments[0];
				return new Point(coordinates, this);
			}
		}
	},
	getCoordinateSequenceFactory: function () {
		return this.coordinateSequenceFactory;
	},
	createPolygon: function () {
		if (arguments.length === 0) {
			return new Polygon(null, null, this);
		} else if (arguments.length === 1) {
			if (hasInterface(arguments[0], CoordinateSequence)) {
				let coordinates = arguments[0];
				return this.createPolygon(this.createLinearRing(coordinates));
			} else if (arguments[0] instanceof Array) {
				let coordinates = arguments[0];
				return this.createPolygon(this.createLinearRing(coordinates));
			} else if (arguments[0] instanceof LinearRing) {
				let shell = arguments[0];
				return this.createPolygon(shell, null);
			}
		} else if (arguments.length === 2) {
			let shell = arguments[0], holes = arguments[1];
			return new Polygon(shell, holes, this);
		}
	},
	getSRID: function () {
		return this.SRID;
	},
	createGeometryCollection: function () {
		if (arguments.length === 0) {
			return new GeometryCollection(null, this);
		} else if (arguments.length === 1) {
			let geometries = arguments[0];
			return new GeometryCollection(geometries, this);
		}
	},
	createGeometry: function (g) {
		var editor = new GeometryEditor(this);
		return editor.edit(g, {
			edit: function () {
				if (arguments.length === 2) {
					let coordSeq = arguments[0];
					return this.coordinateSequenceFactory.create(coordSeq);
				}
			}
		});
	},
	getPrecisionModel: function () {
		return this.precisionModel;
	},
	createLinearRing: function () {
		if (arguments.length === 0) {
			return this.createLinearRing(this.getCoordinateSequenceFactory().create([]));
		} else if (arguments.length === 1) {
			if (arguments[0] instanceof Array) {
				let coordinates = arguments[0];
				return this.createLinearRing(coordinates !== null ? this.getCoordinateSequenceFactory().create(coordinates) : null);
			} else if (hasInterface(arguments[0], CoordinateSequence)) {
				let coordinates = arguments[0];
				return new LinearRing(coordinates, this);
			}
		}
	},
	createMultiPolygon: function () {
		if (arguments.length === 0) {
			return new MultiPolygon(null, this);
		} else if (arguments.length === 1) {
			let polygons = arguments[0];
			return new MultiPolygon(polygons, this);
		}
	},
	createMultiPoint: function () {
		if (arguments.length === 0) {
			return new MultiPoint(null, this);
		} else if (arguments.length === 1) {
			if (arguments[0] instanceof Array) {
				let point = arguments[0];
				return new MultiPoint(point, this);
			} else if (arguments[0] instanceof Array) {
				let coordinates = arguments[0];
				return this.createMultiPoint(coordinates !== null ? this.getCoordinateSequenceFactory().create(coordinates) : null);
			} else if (hasInterface(arguments[0], CoordinateSequence)) {
				let coordinates = arguments[0];
				if (coordinates === null) {
					return this.createMultiPoint(new Array(0).fill(null));
				}
				var points = new Array(coordinates.size()).fill(null);
				for (var i = 0; i < coordinates.size(); i++) {
					var ptSeq = this.getCoordinateSequenceFactory().create(1, coordinates.getDimension());
					CoordinateSequences.copy(coordinates, i, ptSeq, 0, 1);
					points[i] = this.createPoint(ptSeq);
				}
				return this.createMultiPoint(points);
			}
		}
	},
	interfaces_: function () {
		return [Serializable];
	},
	getClass: function () {
		return GeometryFactory;
	}
});
GeometryFactory.toMultiPolygonArray = function (multiPolygons) {
	var multiPolygonArray = new Array(multiPolygons.size()).fill(null);
	return multiPolygons.toArray(multiPolygonArray);
};
GeometryFactory.toGeometryArray = function (geometries) {
	if (geometries === null) return null;
	var geometryArray = new Array(geometries.size()).fill(null);
	return geometries.toArray(geometryArray);
};
GeometryFactory.getDefaultCoordinateSequenceFactory = function () {
	return CoordinateArraySequenceFactory.instance();
};
GeometryFactory.toMultiLineStringArray = function (multiLineStrings) {
	var multiLineStringArray = new Array(multiLineStrings.size()).fill(null);
	return multiLineStrings.toArray(multiLineStringArray);
};
GeometryFactory.toLineStringArray = function (lineStrings) {
	var lineStringArray = new Array(lineStrings.size()).fill(null);
	return lineStrings.toArray(lineStringArray);
};
GeometryFactory.toMultiPointArray = function (multiPoints) {
	var multiPointArray = new Array(multiPoints.size()).fill(null);
	return multiPoints.toArray(multiPointArray);
};
GeometryFactory.toLinearRingArray = function (linearRings) {
	var linearRingArray = new Array(linearRings.size()).fill(null);
	return linearRings.toArray(linearRingArray);
};
GeometryFactory.toPointArray = function (points) {
	var pointArray = new Array(points.size()).fill(null);
	return points.toArray(pointArray);
};
GeometryFactory.toPolygonArray = function (polygons) {
	var polygonArray = new Array(polygons.size()).fill(null);
	return polygons.toArray(polygonArray);
};
GeometryFactory.createPointFromInternalCoord = function (coord, exemplar) {
	exemplar.getPrecisionModel().makePrecise(coord);
	return exemplar.getFactory().createPoint(coord);
};
GeometryFactory.serialVersionUID = -6820524753094095635;

function GeometryCollectionIterator() {
	this.parent = null;
	this.atStart = null;
	this.max = null;
	this.index = null;
	this.subcollectionIterator = null;
	let parent = arguments[0];
	this.parent = parent;
	this.atStart = true;
	this.index = 0;
	this.max = parent.getNumGeometries();
}
extend$1(GeometryCollectionIterator.prototype, {
	next: function () {
		if (this.atStart) {
			this.atStart = false;
			if (GeometryCollectionIterator.isAtomic(this.parent)) this.index++;
			return this.parent;
		}
		if (this.subcollectionIterator !== null) {
			if (this.subcollectionIterator.hasNext()) {
				return this.subcollectionIterator.next();
			} else {
				this.subcollectionIterator = null;
			}
		}
		if (this.index >= this.max) {
			throw new NoSuchElementException();
		}
		var obj = this.parent.getGeometryN(this.index++);
		if (obj instanceof GeometryCollection) {
			this.subcollectionIterator = new GeometryCollectionIterator(obj);
			return this.subcollectionIterator.next();
		}
		return obj;
	},
	remove: function () {
		throw new UnsupportedOperationException(this.getClass().getName());
	},
	hasNext: function () {
		if (this.atStart) {
			return true;
		}
		if (this.subcollectionIterator !== null) {
			if (this.subcollectionIterator.hasNext()) {
				return true;
			}
			this.subcollectionIterator = null;
		}
		if (this.index >= this.max) {
			return false;
		}
		return true;
	},
	interfaces_: function () {
		return [Iterator];
	},
	getClass: function () {
		return GeometryCollectionIterator;
	}
});
GeometryCollectionIterator.isAtomic = function (geom) {
	return !(geom instanceof GeometryCollection);
};

function PointLocator() {
	this.boundaryRule = BoundaryNodeRule.OGC_SFS_BOUNDARY_RULE;
	this.isIn = null;
	this.numBoundaries = null;
	if (arguments.length === 0) {} else if (arguments.length === 1) {
		let boundaryRule = arguments[0];
		if (boundaryRule === null) throw new IllegalArgumentException("Rule must be non-null");
		this.boundaryRule = boundaryRule;
	}
}
extend$1(PointLocator.prototype, {
	locateInternal: function () {
		if (arguments[0] instanceof Coordinate && arguments[1] instanceof Polygon) {
			let p = arguments[0], poly = arguments[1];
			if (poly.isEmpty()) return Location.EXTERIOR;
			var shell = poly.getExteriorRing();
			var shellLoc = this.locateInPolygonRing(p, shell);
			if (shellLoc === Location.EXTERIOR) return Location.EXTERIOR;
			if (shellLoc === Location.BOUNDARY) return Location.BOUNDARY;
			for (var i = 0; i < poly.getNumInteriorRing(); i++) {
				var hole = poly.getInteriorRingN(i);
				var holeLoc = this.locateInPolygonRing(p, hole);
				if (holeLoc === Location.INTERIOR) return Location.EXTERIOR;
				if (holeLoc === Location.BOUNDARY) return Location.BOUNDARY;
			}
			return Location.INTERIOR;
		} else if (arguments[0] instanceof Coordinate && arguments[1] instanceof LineString) {
			let p = arguments[0], l = arguments[1];
			if (!l.getEnvelopeInternal().intersects(p)) return Location.EXTERIOR;
			var pt = l.getCoordinates();
			if (!l.isClosed()) {
				if (p.equals(pt[0]) || p.equals(pt[pt.length - 1])) {
					return Location.BOUNDARY;
				}
			}
			if (CGAlgorithms.isOnLine(p, pt)) return Location.INTERIOR;
			return Location.EXTERIOR;
		} else if (arguments[0] instanceof Coordinate && arguments[1] instanceof Point) {
			let p = arguments[0], pt = arguments[1];
			var ptCoord = pt.getCoordinate();
			if (ptCoord.equals2D(p)) return Location.INTERIOR;
			return Location.EXTERIOR;
		}
	},
	locateInPolygonRing: function (p, ring) {
		if (!ring.getEnvelopeInternal().intersects(p)) return Location.EXTERIOR;
		return CGAlgorithms.locatePointInRing(p, ring.getCoordinates());
	},
	intersects: function (p, geom) {
		return this.locate(p, geom) !== Location.EXTERIOR;
	},
	updateLocationInfo: function (loc) {
		if (loc === Location.INTERIOR) this.isIn = true;
		if (loc === Location.BOUNDARY) this.numBoundaries++;
	},
	computeLocation: function (p, geom) {
		if (geom instanceof Point) {
			this.updateLocationInfo(this.locateInternal(p, geom));
		}
		if (geom instanceof LineString) {
			this.updateLocationInfo(this.locateInternal(p, geom));
		} else if (geom instanceof Polygon) {
			this.updateLocationInfo(this.locateInternal(p, geom));
		} else if (geom instanceof MultiLineString) {
			var ml = geom;
			for (var i = 0; i < ml.getNumGeometries(); i++) {
				var l = ml.getGeometryN(i);
				this.updateLocationInfo(this.locateInternal(p, l));
			}
		} else if (geom instanceof MultiPolygon) {
			var mpoly = geom;
			for (var i = 0; i < mpoly.getNumGeometries(); i++) {
				var poly = mpoly.getGeometryN(i);
				this.updateLocationInfo(this.locateInternal(p, poly));
			}
		} else if (geom instanceof GeometryCollection) {
			var geomi = new GeometryCollectionIterator(geom);
			while (geomi.hasNext()) {
				var g2 = geomi.next();
				if (g2 !== geom) this.computeLocation(p, g2);
			}
		}
	},
	locate: function (p, geom) {
		if (geom.isEmpty()) return Location.EXTERIOR;
		if (geom instanceof LineString) {
			return this.locateInternal(p, geom);
		} else if (geom instanceof Polygon) {
			return this.locateInternal(p, geom);
		}
		this.isIn = false;
		this.numBoundaries = 0;
		this.computeLocation(p, geom);
		if (this.boundaryRule.isInBoundary(this.numBoundaries)) return Location.BOUNDARY;
		if (this.numBoundaries > 0 || this.isIn) return Location.INTERIOR;
		return Location.EXTERIOR;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return PointLocator;
	}
});

function Position() {}
extend$1(Position.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Position;
	}
});
Position.opposite = function (position) {
	if (position === Position.LEFT) return Position.RIGHT;
	if (position === Position.RIGHT) return Position.LEFT;
	return position;
};
Position.ON = 0;
Position.LEFT = 1;
Position.RIGHT = 2;

function MonotoneChain() {
	this.mce = null;
	this.chainIndex = null;
	let mce = arguments[0], chainIndex = arguments[1];
	this.mce = mce;
	this.chainIndex = chainIndex;
}
extend$1(MonotoneChain.prototype, {
	computeIntersections: function (mc, si) {
		this.mce.computeIntersectsForChain(this.chainIndex, mc.mce, mc.chainIndex, si);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return MonotoneChain;
	}
});

function SweepLineEvent() {
	this.label = null;
	this.xValue = null;
	this.eventType = null;
	this.insertEvent = null;
	this.deleteEventIndex = null;
	this.obj = null;
	if (arguments.length === 2) {
		let x = arguments[0], insertEvent = arguments[1];
		this.eventType = SweepLineEvent.DELETE;
		this.xValue = x;
		this.insertEvent = insertEvent;
	} else if (arguments.length === 3) {
		let label = arguments[0], x = arguments[1], obj = arguments[2];
		this.eventType = SweepLineEvent.INSERT;
		this.label = label;
		this.xValue = x;
		this.obj = obj;
	}
}
extend$1(SweepLineEvent.prototype, {
	isDelete: function () {
		return this.eventType === SweepLineEvent.DELETE;
	},
	setDeleteEventIndex: function (deleteEventIndex) {
		this.deleteEventIndex = deleteEventIndex;
	},
	getObject: function () {
		return this.obj;
	},
	compareTo: function (o) {
		var pe = o;
		if (this.xValue < pe.xValue) return -1;
		if (this.xValue > pe.xValue) return 1;
		if (this.eventType < pe.eventType) return -1;
		if (this.eventType > pe.eventType) return 1;
		return 0;
	},
	getInsertEvent: function () {
		return this.insertEvent;
	},
	isInsert: function () {
		return this.eventType === SweepLineEvent.INSERT;
	},
	isSameLabel: function (ev) {
		if (this.label === null) return false;
		return this.label === ev.label;
	},
	getDeleteEventIndex: function () {
		return this.deleteEventIndex;
	},
	interfaces_: function () {
		return [Comparable];
	},
	getClass: function () {
		return SweepLineEvent;
	}
});
SweepLineEvent.INSERT = 1;
SweepLineEvent.DELETE = 2;

function EdgeSetIntersector() {}
extend$1(EdgeSetIntersector.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return EdgeSetIntersector;
	}
});

const Collections = {
  reverseOrder: function () {
    return {
      compare (a, b) {
        return b.compareTo(a)
      }
    }
  },
  min: function (l) {
    Collections.sort(l);
    return l.get(0)
  },
  sort: function (l, c) {
    const a = l.toArray();
    if (c) {
      Arrays.sort(a, c);
    } else {
      Arrays.sort(a);
    }
    const i = l.iterator();
    for (let pos = 0, alen = a.length; pos < alen; pos++) {
      i.next();
      i.set(a[pos]);
    }
  },
  singletonList: function (o) {
    const arrayList = new ArrayList();
    arrayList.add(o);
    return arrayList
  }
};

function SegmentIntersector() {
	this._hasIntersection = false;
	this.hasProper = false;
	this.hasProperInterior = false;
	this.properIntersectionPoint = null;
	this.li = null;
	this.includeProper = null;
	this.recordIsolated = null;
	this.isSelfIntersection = null;
	this.numIntersections = 0;
	this.numTests = 0;
	this.bdyNodes = null;
	this._isDone = false;
	this.isDoneWhenProperInt = false;
	let li = arguments[0], includeProper = arguments[1], recordIsolated = arguments[2];
	this.li = li;
	this.includeProper = includeProper;
	this.recordIsolated = recordIsolated;
}
extend$1(SegmentIntersector.prototype, {
	isTrivialIntersection: function (e0, segIndex0, e1, segIndex1) {
		if (e0 === e1) {
			if (this.li.getIntersectionNum() === 1) {
				if (SegmentIntersector.isAdjacentSegments(segIndex0, segIndex1)) return true;
				if (e0.isClosed()) {
					var maxSegIndex = e0.getNumPoints() - 1;
					if (segIndex0 === 0 && segIndex1 === maxSegIndex || segIndex1 === 0 && segIndex0 === maxSegIndex) {
						return true;
					}
				}
			}
		}
		return false;
	},
	getProperIntersectionPoint: function () {
		return this.properIntersectionPoint;
	},
	setIsDoneIfProperInt: function (isDoneWhenProperInt) {
		this.isDoneWhenProperInt = isDoneWhenProperInt;
	},
	hasProperInteriorIntersection: function () {
		return this.hasProperInterior;
	},
	isBoundaryPointInternal: function (li, bdyNodes) {
		for (var i = bdyNodes.iterator(); i.hasNext(); ) {
			var node = i.next();
			var pt = node.getCoordinate();
			if (li.isIntersection(pt)) return true;
		}
		return false;
	},
	hasProperIntersection: function () {
		return this.hasProper;
	},
	hasIntersection: function () {
		return this._hasIntersection;
	},
	isDone: function () {
		return this._isDone;
	},
	isBoundaryPoint: function (li, bdyNodes) {
		if (bdyNodes === null) return false;
		if (this.isBoundaryPointInternal(li, bdyNodes[0])) return true;
		if (this.isBoundaryPointInternal(li, bdyNodes[1])) return true;
		return false;
	},
	setBoundaryNodes: function (bdyNodes0, bdyNodes1) {
		this.bdyNodes = new Array(2).fill(null);
		this.bdyNodes[0] = bdyNodes0;
		this.bdyNodes[1] = bdyNodes1;
	},
	addIntersections: function (e0, segIndex0, e1, segIndex1) {
		if (e0 === e1 && segIndex0 === segIndex1) return null;
		this.numTests++;
		var p00 = e0.getCoordinates()[segIndex0];
		var p01 = e0.getCoordinates()[segIndex0 + 1];
		var p10 = e1.getCoordinates()[segIndex1];
		var p11 = e1.getCoordinates()[segIndex1 + 1];
		this.li.computeIntersection(p00, p01, p10, p11);
		if (this.li.hasIntersection()) {
			if (this.recordIsolated) {
				e0.setIsolated(false);
				e1.setIsolated(false);
			}
			this.numIntersections++;
			if (!this.isTrivialIntersection(e0, segIndex0, e1, segIndex1)) {
				this._hasIntersection = true;
				if (this.includeProper || !this.li.isProper()) {
					e0.addIntersections(this.li, segIndex0, 0);
					e1.addIntersections(this.li, segIndex1, 1);
				}
				if (this.li.isProper()) {
					this.properIntersectionPoint = this.li.getIntersection(0).copy();
					this.hasProper = true;
					if (this.isDoneWhenProperInt) {
						this._isDone = true;
					}
					if (!this.isBoundaryPoint(this.li, this.bdyNodes)) this.hasProperInterior = true;
				}
			}
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return SegmentIntersector;
	}
});
SegmentIntersector.isAdjacentSegments = function (i1, i2) {
	return Math.abs(i1 - i2) === 1;
};

function SimpleMCSweepLineIntersector() {
	EdgeSetIntersector.apply(this);
	this.events = new ArrayList();
	this.nOverlaps = null;
}
inherits(SimpleMCSweepLineIntersector, EdgeSetIntersector);
extend$1(SimpleMCSweepLineIntersector.prototype, {
	prepareEvents: function () {
		Collections.sort(this.events);
		for (var i = 0; i < this.events.size(); i++) {
			var ev = this.events.get(i);
			if (ev.isDelete()) {
				ev.getInsertEvent().setDeleteEventIndex(i);
			}
		}
	},
	computeIntersections: function () {
		if (arguments.length === 1) {
			let si = arguments[0];
			this.nOverlaps = 0;
			this.prepareEvents();
			for (var i = 0; i < this.events.size(); i++) {
				var ev = this.events.get(i);
				if (ev.isInsert()) {
					this.processOverlaps(i, ev.getDeleteEventIndex(), ev, si);
				}
				if (si.isDone()) {
					break;
				}
			}
		} else if (arguments.length === 3) {
			if (arguments[2] instanceof SegmentIntersector && (hasInterface(arguments[0], List) && hasInterface(arguments[1], List))) {
				let edges0 = arguments[0], edges1 = arguments[1], si = arguments[2];
				this.addEdges(edges0, edges0);
				this.addEdges(edges1, edges1);
				this.computeIntersections(si);
			} else if (typeof arguments[2] === "boolean" && (hasInterface(arguments[0], List) && arguments[1] instanceof SegmentIntersector)) {
				let edges = arguments[0], si = arguments[1], testAllSegments = arguments[2];
				if (testAllSegments) this.addEdges(edges, null); else this.addEdges(edges);
				this.computeIntersections(si);
			}
		}
	},
	addEdge: function (edge, edgeSet) {
		var mce = edge.getMonotoneChainEdge();
		var startIndex = mce.getStartIndexes();
		for (var i = 0; i < startIndex.length - 1; i++) {
			var mc = new MonotoneChain(mce, i);
			var insertEvent = new SweepLineEvent(edgeSet, mce.getMinX(i), mc);
			this.events.add(insertEvent);
			this.events.add(new SweepLineEvent(mce.getMaxX(i), insertEvent));
		}
	},
	processOverlaps: function (start, end, ev0, si) {
		var mc0 = ev0.getObject();
		for (var i = start; i < end; i++) {
			var ev1 = this.events.get(i);
			if (ev1.isInsert()) {
				var mc1 = ev1.getObject();
				if (!ev0.isSameLabel(ev1)) {
					mc0.computeIntersections(mc1, si);
					this.nOverlaps++;
				}
			}
		}
	},
	addEdges: function () {
		if (arguments.length === 1) {
			let edges = arguments[0];
			for (var i = edges.iterator(); i.hasNext(); ) {
				var edge = i.next();
				this.addEdge(edge, edge);
			}
		} else if (arguments.length === 2) {
			let edges = arguments[0], edgeSet = arguments[1];
			for (var i = edges.iterator(); i.hasNext(); ) {
				var edge = i.next();
				this.addEdge(edge, edgeSet);
			}
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return SimpleMCSweepLineIntersector;
	}
});

function TopologyLocation() {
	this.location = null;
	if (arguments.length === 1) {
		if (arguments[0] instanceof Array) {
			let location = arguments[0];
			this.init(location.length);
		} else if (Number.isInteger(arguments[0])) {
			let on = arguments[0];
			this.init(1);
			this.location[Position.ON] = on;
		} else if (arguments[0] instanceof TopologyLocation) {
			let gl = arguments[0];
			this.init(gl.location.length);
			if (gl !== null) {
				for (var i = 0; i < this.location.length; i++) {
					this.location[i] = gl.location[i];
				}
			}
		}
	} else if (arguments.length === 3) {
		let on = arguments[0], left = arguments[1], right = arguments[2];
		this.init(3);
		this.location[Position.ON] = on;
		this.location[Position.LEFT] = left;
		this.location[Position.RIGHT] = right;
	}
}
extend$1(TopologyLocation.prototype, {
	setAllLocations: function (locValue) {
		for (var i = 0; i < this.location.length; i++) {
			this.location[i] = locValue;
		}
	},
	isNull: function () {
		for (var i = 0; i < this.location.length; i++) {
			if (this.location[i] !== Location.NONE) return false;
		}
		return true;
	},
	setAllLocationsIfNull: function (locValue) {
		for (var i = 0; i < this.location.length; i++) {
			if (this.location[i] === Location.NONE) this.location[i] = locValue;
		}
	},
	isLine: function () {
		return this.location.length === 1;
	},
	merge: function (gl) {
		if (gl.location.length > this.location.length) {
			var newLoc = new Array(3).fill(null);
			newLoc[Position.ON] = this.location[Position.ON];
			newLoc[Position.LEFT] = Location.NONE;
			newLoc[Position.RIGHT] = Location.NONE;
			this.location = newLoc;
		}
		for (var i = 0; i < this.location.length; i++) {
			if (this.location[i] === Location.NONE && i < gl.location.length) this.location[i] = gl.location[i];
		}
	},
	getLocations: function () {
		return this.location;
	},
	flip: function () {
		if (this.location.length <= 1) return null;
		var temp = this.location[Position.LEFT];
		this.location[Position.LEFT] = this.location[Position.RIGHT];
		this.location[Position.RIGHT] = temp;
	},
	toString: function () {
		var buf = new StringBuffer();
		if (this.location.length > 1) buf.append(Location.toLocationSymbol(this.location[Position.LEFT]));
		buf.append(Location.toLocationSymbol(this.location[Position.ON]));
		if (this.location.length > 1) buf.append(Location.toLocationSymbol(this.location[Position.RIGHT]));
		return buf.toString();
	},
	setLocations: function (on, left, right) {
		this.location[Position.ON] = on;
		this.location[Position.LEFT] = left;
		this.location[Position.RIGHT] = right;
	},
	get: function (posIndex) {
		if (posIndex < this.location.length) return this.location[posIndex];
		return Location.NONE;
	},
	isArea: function () {
		return this.location.length > 1;
	},
	isAnyNull: function () {
		for (var i = 0; i < this.location.length; i++) {
			if (this.location[i] === Location.NONE) return true;
		}
		return false;
	},
	setLocation: function () {
		if (arguments.length === 1) {
			let locValue = arguments[0];
			this.setLocation(Position.ON, locValue);
		} else if (arguments.length === 2) {
			let locIndex = arguments[0], locValue = arguments[1];
			this.location[locIndex] = locValue;
		}
	},
	init: function (size) {
		this.location = new Array(size).fill(null);
		this.setAllLocations(Location.NONE);
	},
	isEqualOnSide: function (le, locIndex) {
		return this.location[locIndex] === le.location[locIndex];
	},
	allPositionsEqual: function (loc) {
		for (var i = 0; i < this.location.length; i++) {
			if (this.location[i] !== loc) return false;
		}
		return true;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return TopologyLocation;
	}
});

function Label() {
	this.elt = new Array(2).fill(null);
	if (arguments.length === 1) {
		if (Number.isInteger(arguments[0])) {
			let onLoc = arguments[0];
			this.elt[0] = new TopologyLocation(onLoc);
			this.elt[1] = new TopologyLocation(onLoc);
		} else if (arguments[0] instanceof Label) {
			let lbl = arguments[0];
			this.elt[0] = new TopologyLocation(lbl.elt[0]);
			this.elt[1] = new TopologyLocation(lbl.elt[1]);
		}
	} else if (arguments.length === 2) {
		let geomIndex = arguments[0], onLoc = arguments[1];
		this.elt[0] = new TopologyLocation(Location.NONE);
		this.elt[1] = new TopologyLocation(Location.NONE);
		this.elt[geomIndex].setLocation(onLoc);
	} else if (arguments.length === 3) {
		let onLoc = arguments[0], leftLoc = arguments[1], rightLoc = arguments[2];
		this.elt[0] = new TopologyLocation(onLoc, leftLoc, rightLoc);
		this.elt[1] = new TopologyLocation(onLoc, leftLoc, rightLoc);
	} else if (arguments.length === 4) {
		let geomIndex = arguments[0], onLoc = arguments[1], leftLoc = arguments[2], rightLoc = arguments[3];
		this.elt[0] = new TopologyLocation(Location.NONE, Location.NONE, Location.NONE);
		this.elt[1] = new TopologyLocation(Location.NONE, Location.NONE, Location.NONE);
		this.elt[geomIndex].setLocations(onLoc, leftLoc, rightLoc);
	}
}
extend$1(Label.prototype, {
	getGeometryCount: function () {
		var count = 0;
		if (!this.elt[0].isNull()) count++;
		if (!this.elt[1].isNull()) count++;
		return count;
	},
	setAllLocations: function (geomIndex, location) {
		this.elt[geomIndex].setAllLocations(location);
	},
	isNull: function (geomIndex) {
		return this.elt[geomIndex].isNull();
	},
	setAllLocationsIfNull: function () {
		if (arguments.length === 1) {
			let location = arguments[0];
			this.setAllLocationsIfNull(0, location);
			this.setAllLocationsIfNull(1, location);
		} else if (arguments.length === 2) {
			let geomIndex = arguments[0], location = arguments[1];
			this.elt[geomIndex].setAllLocationsIfNull(location);
		}
	},
	isLine: function (geomIndex) {
		return this.elt[geomIndex].isLine();
	},
	merge: function (lbl) {
		for (var i = 0; i < 2; i++) {
			if (this.elt[i] === null && lbl.elt[i] !== null) {
				this.elt[i] = new TopologyLocation(lbl.elt[i]);
			} else {
				this.elt[i].merge(lbl.elt[i]);
			}
		}
	},
	flip: function () {
		this.elt[0].flip();
		this.elt[1].flip();
	},
	getLocation: function () {
		if (arguments.length === 1) {
			let geomIndex = arguments[0];
			return this.elt[geomIndex].get(Position.ON);
		} else if (arguments.length === 2) {
			let geomIndex = arguments[0], posIndex = arguments[1];
			return this.elt[geomIndex].get(posIndex);
		}
	},
	toString: function () {
		var buf = new StringBuffer();
		if (this.elt[0] !== null) {
			buf.append("A:");
			buf.append(this.elt[0].toString());
		}
		if (this.elt[1] !== null) {
			buf.append(" B:");
			buf.append(this.elt[1].toString());
		}
		return buf.toString();
	},
	isArea: function () {
		if (arguments.length === 0) {
			return this.elt[0].isArea() || this.elt[1].isArea();
		} else if (arguments.length === 1) {
			let geomIndex = arguments[0];
			return this.elt[geomIndex].isArea();
		}
	},
	isAnyNull: function (geomIndex) {
		return this.elt[geomIndex].isAnyNull();
	},
	setLocation: function () {
		if (arguments.length === 2) {
			let geomIndex = arguments[0], location = arguments[1];
			this.elt[geomIndex].setLocation(Position.ON, location);
		} else if (arguments.length === 3) {
			let geomIndex = arguments[0], posIndex = arguments[1], location = arguments[2];
			this.elt[geomIndex].setLocation(posIndex, location);
		}
	},
	isEqualOnSide: function (lbl, side) {
		return this.elt[0].isEqualOnSide(lbl.elt[0], side) && this.elt[1].isEqualOnSide(lbl.elt[1], side);
	},
	allPositionsEqual: function (geomIndex, loc) {
		return this.elt[geomIndex].allPositionsEqual(loc);
	},
	toLine: function (geomIndex) {
		if (this.elt[geomIndex].isArea()) this.elt[geomIndex] = new TopologyLocation(this.elt[geomIndex].location[0]);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Label;
	}
});
Label.toLineLabel = function (label) {
	var lineLabel = new Label(Location.NONE);
	for (var i = 0; i < 2; i++) {
		lineLabel.setLocation(i, label.getLocation(i));
	}
	return lineLabel;
};

function ItemVisitor() {}
extend$1(ItemVisitor.prototype, {
	visitItem: function (item) {},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return ItemVisitor;
	}
});

function PointOnGeometryLocator() {}
extend$1(PointOnGeometryLocator.prototype, {
	locate: function (p) {},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return PointOnGeometryLocator;
	}
});

function IntervalRTreeNode$1() {
	this.min = Double.POSITIVE_INFINITY;
	this.max = Double.NEGATIVE_INFINITY;
}
extend$1(IntervalRTreeNode$1.prototype, {
	getMin: function () {
		return this.min;
	},
	intersects: function (queryMin, queryMax) {
		if (this.min > queryMax || this.max < queryMin) return false;
		return true;
	},
	getMax: function () {
		return this.max;
	},
	toString: function () {
		return WKTWriter.toLineString(new Coordinate(this.min, 0), new Coordinate(this.max, 0));
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return IntervalRTreeNode$1;
	}
});
function NodeComparator() {}
extend$1(NodeComparator.prototype, {
	compare: function (o1, o2) {
		var n1 = o1;
		var n2 = o2;
		var mid1 = (n1.min + n1.max) / 2;
		var mid2 = (n2.min + n2.max) / 2;
		if (mid1 < mid2) return -1;
		if (mid1 > mid2) return 1;
		return 0;
	},
	interfaces_: function () {
		return [Comparator];
	},
	getClass: function () {
		return NodeComparator;
	}
});
IntervalRTreeNode$1.NodeComparator = NodeComparator;

function IntervalRTreeLeafNode() {
	IntervalRTreeNode$1.apply(this);
	this.item = null;
	let min = arguments[0], max = arguments[1], item = arguments[2];
	this.min = min;
	this.max = max;
	this.item = item;
}
inherits(IntervalRTreeLeafNode, IntervalRTreeNode$1);
extend$1(IntervalRTreeLeafNode.prototype, {
	query: function (queryMin, queryMax, visitor) {
		if (!this.intersects(queryMin, queryMax)) return null;
		visitor.visitItem(this.item);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return IntervalRTreeLeafNode;
	}
});

function IntervalRTreeBranchNode() {
	IntervalRTreeNode$1.apply(this);
	this.node1 = null;
	this.node2 = null;
	let n1 = arguments[0], n2 = arguments[1];
	this.node1 = n1;
	this.node2 = n2;
	this.buildExtent(this.node1, this.node2);
}
inherits(IntervalRTreeBranchNode, IntervalRTreeNode$1);
extend$1(IntervalRTreeBranchNode.prototype, {
	buildExtent: function (n1, n2) {
		this.min = Math.min(n1.min, n2.min);
		this.max = Math.max(n1.max, n2.max);
	},
	query: function (queryMin, queryMax, visitor) {
		if (!this.intersects(queryMin, queryMax)) {
			return null;
		}
		if (this.node1 !== null) this.node1.query(queryMin, queryMax, visitor);
		if (this.node2 !== null) this.node2.query(queryMin, queryMax, visitor);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return IntervalRTreeBranchNode;
	}
});

function SortedPackedIntervalRTree() {
	this.leaves = new ArrayList();
	this.root = null;
	this.level = 0;
}
extend$1(SortedPackedIntervalRTree.prototype, {
	buildTree: function () {
		Collections.sort(this.leaves, new IntervalRTreeNode.NodeComparator());
		var src = this.leaves;
		var temp = null;
		var dest = new ArrayList();
		while (true) {
			this.buildLevel(src, dest);
			if (dest.size() === 1) return dest.get(0);
			temp = src;
			src = dest;
			dest = temp;
		}
	},
	insert: function (min, max, item) {
		if (this.root !== null) throw new IllegalStateException("Index cannot be added to once it has been queried");
		this.leaves.add(new IntervalRTreeLeafNode(min, max, item));
	},
	query: function (min, max, visitor) {
		this.init();
		this.root.query(min, max, visitor);
	},
	buildRoot: function () {
		if (this.root !== null) return null;
		this.root = this.buildTree();
	},
	printNode: function (node) {
		System.out.println(WKTWriter.toLineString(new Coordinate(node.min, this.level), new Coordinate(node.max, this.level)));
	},
	init: function () {
		if (this.root !== null) return null;
		this.buildRoot();
	},
	buildLevel: function (src, dest) {
		this.level++;
		dest.clear();
		for (var i = 0; i < src.size(); i += 2) {
			var n1 = src.get(i);
			var n2 = i + 1 < src.size() ? src.get(i) : null;
			if (n2 === null) {
				dest.add(n1);
			} else {
				var node = new IntervalRTreeBranchNode(src.get(i), src.get(i + 1));
				dest.add(node);
			}
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return SortedPackedIntervalRTree;
	}
});

function LineSegment() {
	this.p0 = null;
	this.p1 = null;
	if (arguments.length === 0) {
		LineSegment.call(this, new Coordinate(), new Coordinate());
	} else if (arguments.length === 1) {
		let ls = arguments[0];
		LineSegment.call(this, ls.p0, ls.p1);
	} else if (arguments.length === 2) {
		let p0 = arguments[0], p1 = arguments[1];
		this.p0 = p0;
		this.p1 = p1;
	} else if (arguments.length === 4) {
		let x0 = arguments[0], y0 = arguments[1], x1 = arguments[2], y1 = arguments[3];
		LineSegment.call(this, new Coordinate(x0, y0), new Coordinate(x1, y1));
	}
}
extend$1(LineSegment.prototype, {
	minX: function () {
		return Math.min(this.p0.x, this.p1.x);
	},
	orientationIndex: function () {
		if (arguments[0] instanceof LineSegment) {
			let seg = arguments[0];
			var orient0 = CGAlgorithms.orientationIndex(this.p0, this.p1, seg.p0);
			var orient1 = CGAlgorithms.orientationIndex(this.p0, this.p1, seg.p1);
			if (orient0 >= 0 && orient1 >= 0) return Math.max(orient0, orient1);
			if (orient0 <= 0 && orient1 <= 0) return Math.max(orient0, orient1);
			return 0;
		} else if (arguments[0] instanceof Coordinate) {
			let p = arguments[0];
			return CGAlgorithms.orientationIndex(this.p0, this.p1, p);
		}
	},
	toGeometry: function (geomFactory) {
		return geomFactory.createLineString([this.p0, this.p1]);
	},
	isVertical: function () {
		return this.p0.x === this.p1.x;
	},
	equals: function (o) {
		if (!(o instanceof LineSegment)) {
			return false;
		}
		var other = o;
		return this.p0.equals(other.p0) && this.p1.equals(other.p1);
	},
	intersection: function (line) {
		var li = new RobustLineIntersector();
		li.computeIntersection(this.p0, this.p1, line.p0, line.p1);
		if (li.hasIntersection()) return li.getIntersection(0);
		return null;
	},
	project: function () {
		if (arguments[0] instanceof Coordinate) {
			let p = arguments[0];
			if (p.equals(this.p0) || p.equals(this.p1)) return new Coordinate(p);
			var r = this.projectionFactor(p);
			var coord = new Coordinate();
			coord.x = this.p0.x + r * (this.p1.x - this.p0.x);
			coord.y = this.p0.y + r * (this.p1.y - this.p0.y);
			return coord;
		} else if (arguments[0] instanceof LineSegment) {
			let seg = arguments[0];
			var pf0 = this.projectionFactor(seg.p0);
			var pf1 = this.projectionFactor(seg.p1);
			if (pf0 >= 1.0 && pf1 >= 1.0) return null;
			if (pf0 <= 0.0 && pf1 <= 0.0) return null;
			var newp0 = this.project(seg.p0);
			if (pf0 < 0.0) newp0 = this.p0;
			if (pf0 > 1.0) newp0 = this.p1;
			var newp1 = this.project(seg.p1);
			if (pf1 < 0.0) newp1 = this.p0;
			if (pf1 > 1.0) newp1 = this.p1;
			return new LineSegment(newp0, newp1);
		}
	},
	normalize: function () {
		if (this.p1.compareTo(this.p0) < 0) this.reverse();
	},
	angle: function () {
		return Math.atan2(this.p1.y - this.p0.y, this.p1.x - this.p0.x);
	},
	getCoordinate: function (i) {
		if (i === 0) return this.p0;
		return this.p1;
	},
	distancePerpendicular: function (p) {
		return CGAlgorithms.distancePointLinePerpendicular(p, this.p0, this.p1);
	},
	minY: function () {
		return Math.min(this.p0.y, this.p1.y);
	},
	midPoint: function () {
		return LineSegment.midPoint(this.p0, this.p1);
	},
	projectionFactor: function (p) {
		if (p.equals(this.p0)) return 0.0;
		if (p.equals(this.p1)) return 1.0;
		var dx = this.p1.x - this.p0.x;
		var dy = this.p1.y - this.p0.y;
		var len = dx * dx + dy * dy;
		if (len <= 0.0) return Double.NaN;
		var r = ((p.x - this.p0.x) * dx + (p.y - this.p0.y) * dy) / len;
		return r;
	},
	closestPoints: function (line) {
		var intPt = this.intersection(line);
		if (intPt !== null) {
			return [intPt, intPt];
		}
		var closestPt = new Array(2).fill(null);
		var minDistance = Double.MAX_VALUE;
		var dist = null;
		var close00 = this.closestPoint(line.p0);
		minDistance = close00.distance(line.p0);
		closestPt[0] = close00;
		closestPt[1] = line.p0;
		var close01 = this.closestPoint(line.p1);
		dist = close01.distance(line.p1);
		if (dist < minDistance) {
			minDistance = dist;
			closestPt[0] = close01;
			closestPt[1] = line.p1;
		}
		var close10 = line.closestPoint(this.p0);
		dist = close10.distance(this.p0);
		if (dist < minDistance) {
			minDistance = dist;
			closestPt[0] = this.p0;
			closestPt[1] = close10;
		}
		var close11 = line.closestPoint(this.p1);
		dist = close11.distance(this.p1);
		if (dist < minDistance) {
			minDistance = dist;
			closestPt[0] = this.p1;
			closestPt[1] = close11;
		}
		return closestPt;
	},
	closestPoint: function (p) {
		var factor = this.projectionFactor(p);
		if (factor > 0 && factor < 1) {
			return this.project(p);
		}
		var dist0 = this.p0.distance(p);
		var dist1 = this.p1.distance(p);
		if (dist0 < dist1) return this.p0;
		return this.p1;
	},
	maxX: function () {
		return Math.max(this.p0.x, this.p1.x);
	},
	getLength: function () {
		return this.p0.distance(this.p1);
	},
	compareTo: function (o) {
		var other = o;
		var comp0 = this.p0.compareTo(other.p0);
		if (comp0 !== 0) return comp0;
		return this.p1.compareTo(other.p1);
	},
	reverse: function () {
		var temp = this.p0;
		this.p0 = this.p1;
		this.p1 = temp;
	},
	equalsTopo: function (other) {
		return this.p0.equals(other.p0) && this.p1.equals(other.p1) || this.p0.equals(other.p1) && this.p1.equals(other.p0);
	},
	lineIntersection: function (line) {
		try {
			var intPt = HCoordinate.intersection(this.p0, this.p1, line.p0, line.p1);
			return intPt;
		} catch (ex) {
			if (ex instanceof NotRepresentableException) {} else throw ex;
		} finally {}
		return null;
	},
	maxY: function () {
		return Math.max(this.p0.y, this.p1.y);
	},
	pointAlongOffset: function (segmentLengthFraction, offsetDistance) {
		var segx = this.p0.x + segmentLengthFraction * (this.p1.x - this.p0.x);
		var segy = this.p0.y + segmentLengthFraction * (this.p1.y - this.p0.y);
		var dx = this.p1.x - this.p0.x;
		var dy = this.p1.y - this.p0.y;
		var len = Math.sqrt(dx * dx + dy * dy);
		var ux = 0.0;
		var uy = 0.0;
		if (offsetDistance !== 0.0) {
			if (len <= 0.0) throw new IllegalStateException("Cannot compute offset from zero-length line segment");
			ux = offsetDistance * dx / len;
			uy = offsetDistance * dy / len;
		}
		var offsetx = segx - uy;
		var offsety = segy + ux;
		var coord = new Coordinate(offsetx, offsety);
		return coord;
	},
	setCoordinates: function () {
		if (arguments.length === 1) {
			let ls = arguments[0];
			this.setCoordinates(ls.p0, ls.p1);
		} else if (arguments.length === 2) {
			let p0 = arguments[0], p1 = arguments[1];
			this.p0.x = p0.x;
			this.p0.y = p0.y;
			this.p1.x = p1.x;
			this.p1.y = p1.y;
		}
	},
	segmentFraction: function (inputPt) {
		var segFrac = this.projectionFactor(inputPt);
		if (segFrac < 0.0) segFrac = 0.0; else if (segFrac > 1.0 || Double.isNaN(segFrac)) segFrac = 1.0;
		return segFrac;
	},
	toString: function () {
		return "LINESTRING( " + this.p0.x + " " + this.p0.y + ", " + this.p1.x + " " + this.p1.y + ")";
	},
	isHorizontal: function () {
		return this.p0.y === this.p1.y;
	},
	distance: function () {
		if (arguments[0] instanceof LineSegment) {
			let ls = arguments[0];
			return CGAlgorithms.distanceLineLine(this.p0, this.p1, ls.p0, ls.p1);
		} else if (arguments[0] instanceof Coordinate) {
			let p = arguments[0];
			return CGAlgorithms.distancePointLine(p, this.p0, this.p1);
		}
	},
	pointAlong: function (segmentLengthFraction) {
		var coord = new Coordinate();
		coord.x = this.p0.x + segmentLengthFraction * (this.p1.x - this.p0.x);
		coord.y = this.p0.y + segmentLengthFraction * (this.p1.y - this.p0.y);
		return coord;
	},
	hashCode: function () {
		var bits0 = java.lang.Double.doubleToLongBits(this.p0.x);
		bits0 ^= java.lang.Double.doubleToLongBits(this.p0.y) * 31;
		var hash0 = Math.trunc(bits0) ^ Math.trunc(bits0 >> 32);
		var bits1 = java.lang.Double.doubleToLongBits(this.p1.x);
		bits1 ^= java.lang.Double.doubleToLongBits(this.p1.y) * 31;
		var hash1 = Math.trunc(bits1) ^ Math.trunc(bits1 >> 32);
		return hash0 ^ hash1;
	},
	interfaces_: function () {
		return [Comparable, Serializable];
	},
	getClass: function () {
		return LineSegment;
	}
});
LineSegment.midPoint = function (p0, p1) {
	return new Coordinate((p0.x + p1.x) / 2, (p0.y + p1.y) / 2);
};
LineSegment.serialVersionUID = 3252005833466256227;

function LinearComponentExtracter() {
	this.lines = null;
	this.isForcedToLineString = false;
	if (arguments.length === 1) {
		let lines = arguments[0];
		this.lines = lines;
	} else if (arguments.length === 2) {
		let lines = arguments[0], isForcedToLineString = arguments[1];
		this.lines = lines;
		this.isForcedToLineString = isForcedToLineString;
	}
}
extend$1(LinearComponentExtracter.prototype, {
	filter: function (geom) {
		if (this.isForcedToLineString && geom instanceof LinearRing) {
			var line = geom.getFactory().createLineString(geom.getCoordinateSequence());
			this.lines.add(line);
			return null;
		}
		if (geom instanceof LineString) this.lines.add(geom);
	},
	setForceToLineString: function (isForcedToLineString) {
		this.isForcedToLineString = isForcedToLineString;
	},
	interfaces_: function () {
		return [GeometryComponentFilter];
	},
	getClass: function () {
		return LinearComponentExtracter;
	}
});
LinearComponentExtracter.getGeometry = function () {
	if (arguments.length === 1) {
		let geom = arguments[0];
		return geom.getFactory().buildGeometry(LinearComponentExtracter.getLines(geom));
	} else if (arguments.length === 2) {
		let geom = arguments[0], forceToLineString = arguments[1];
		return geom.getFactory().buildGeometry(LinearComponentExtracter.getLines(geom, forceToLineString));
	}
};
LinearComponentExtracter.getLines = function () {
	if (arguments.length === 1) {
		let geom = arguments[0];
		return LinearComponentExtracter.getLines(geom, false);
	} else if (arguments.length === 2) {
		if (hasInterface(arguments[0], Collection) && hasInterface(arguments[1], Collection)) {
			let geoms = arguments[0], lines = arguments[1];
			for (var i = geoms.iterator(); i.hasNext(); ) {
				var g = i.next();
				LinearComponentExtracter.getLines(g, lines);
			}
			return lines;
		} else if (arguments[0] instanceof Geometry && typeof arguments[1] === "boolean") {
			let geom = arguments[0], forceToLineString = arguments[1];
			var lines = new ArrayList();
			geom.apply(new LinearComponentExtracter(lines, forceToLineString));
			return lines;
		} else if (arguments[0] instanceof Geometry && hasInterface(arguments[1], Collection)) {
			let geom = arguments[0], lines = arguments[1];
			if (geom instanceof LineString) {
				lines.add(geom);
			} else {
				geom.apply(new LinearComponentExtracter(lines));
			}
			return lines;
		}
	} else if (arguments.length === 3) {
		if (typeof arguments[2] === "boolean" && (hasInterface(arguments[0], Collection) && hasInterface(arguments[1], Collection))) {
			let geoms = arguments[0], lines = arguments[1], forceToLineString = arguments[2];
			for (var i = geoms.iterator(); i.hasNext(); ) {
				var g = i.next();
				LinearComponentExtracter.getLines(g, lines, forceToLineString);
			}
			return lines;
		} else if (typeof arguments[2] === "boolean" && (arguments[0] instanceof Geometry && hasInterface(arguments[1], Collection))) {
			let geom = arguments[0], lines = arguments[1], forceToLineString = arguments[2];
			geom.apply(new LinearComponentExtracter(lines, forceToLineString));
			return lines;
		}
	}
};

function ArrayListVisitor() {
	this.items = new ArrayList();
}
extend$1(ArrayListVisitor.prototype, {
	visitItem: function (item) {
		this.items.add(item);
	},
	getItems: function () {
		return this.items;
	},
	interfaces_: function () {
		return [ItemVisitor];
	},
	getClass: function () {
		return ArrayListVisitor;
	}
});

function IndexedPointInAreaLocator() {
	this.index = null;
	let g = arguments[0];
	if (!hasInterface(g, Polygonal)) throw new IllegalArgumentException("Argument must be Polygonal");
	this.index = new IntervalIndexedGeometry(g);
}
extend$1(IndexedPointInAreaLocator.prototype, {
	locate: function (p) {
		var rcc = new RayCrossingCounter(p);
		var visitor = new SegmentVisitor(rcc);
		this.index.query(p.y, p.y, visitor);
		return rcc.getLocation();
	},
	interfaces_: function () {
		return [PointOnGeometryLocator];
	},
	getClass: function () {
		return IndexedPointInAreaLocator;
	}
});
function SegmentVisitor() {
	this.counter = null;
	let counter = arguments[0];
	this.counter = counter;
}
extend$1(SegmentVisitor.prototype, {
	visitItem: function (item) {
		var seg = item;
		this.counter.countSegment(seg.getCoordinate(0), seg.getCoordinate(1));
	},
	interfaces_: function () {
		return [ItemVisitor];
	},
	getClass: function () {
		return SegmentVisitor;
	}
});
function IntervalIndexedGeometry() {
	this.index = new SortedPackedIntervalRTree();
	let geom = arguments[0];
	this.init(geom);
}
extend$1(IntervalIndexedGeometry.prototype, {
	init: function (geom) {
		var lines = LinearComponentExtracter.getLines(geom);
		for (var i = lines.iterator(); i.hasNext(); ) {
			var line = i.next();
			var pts = line.getCoordinates();
			this.addLine(pts);
		}
	},
	addLine: function (pts) {
		for (var i = 1; i < pts.length; i++) {
			var seg = new LineSegment(pts[i - 1], pts[i]);
			var min = Math.min(seg.p0.y, seg.p1.y);
			var max = Math.max(seg.p0.y, seg.p1.y);
			this.index.insert(min, max, seg);
		}
	},
	query: function () {
		if (arguments.length === 2) {
			let min = arguments[0], max = arguments[1];
			var visitor = new ArrayListVisitor();
			this.index.query(min, max, visitor);
			return visitor.getItems();
		} else if (arguments.length === 3) {
			let min = arguments[0], max = arguments[1], visitor = arguments[2];
			this.index.query(min, max, visitor);
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return IntervalIndexedGeometry;
	}
});
IndexedPointInAreaLocator.SegmentVisitor = SegmentVisitor;
IndexedPointInAreaLocator.IntervalIndexedGeometry = IntervalIndexedGeometry;

function EdgeIntersection() {
	this.coord = null;
	this.segmentIndex = null;
	this.dist = null;
	let coord = arguments[0], segmentIndex = arguments[1], dist = arguments[2];
	this.coord = new Coordinate(coord);
	this.segmentIndex = segmentIndex;
	this.dist = dist;
}
extend$1(EdgeIntersection.prototype, {
	getSegmentIndex: function () {
		return this.segmentIndex;
	},
	getCoordinate: function () {
		return this.coord;
	},
	print: function (out) {
		out.print(this.coord);
		out.print(" seg # = " + this.segmentIndex);
		out.println(" dist = " + this.dist);
	},
	compareTo: function (obj) {
		var other = obj;
		return this.compare(other.segmentIndex, other.dist);
	},
	isEndPoint: function (maxSegmentIndex) {
		if (this.segmentIndex === 0 && this.dist === 0.0) return true;
		if (this.segmentIndex === maxSegmentIndex) return true;
		return false;
	},
	toString: function () {
		return this.coord + " seg # = " + this.segmentIndex + " dist = " + this.dist;
	},
	getDistance: function () {
		return this.dist;
	},
	compare: function (segmentIndex, dist) {
		if (this.segmentIndex < segmentIndex) return -1;
		if (this.segmentIndex > segmentIndex) return 1;
		if (this.dist < dist) return -1;
		if (this.dist > dist) return 1;
		return 0;
	},
	interfaces_: function () {
		return [Comparable];
	},
	getClass: function () {
		return EdgeIntersection;
	}
});

function EdgeIntersectionList() {
	this.nodeMap = new TreeMap();
	this.edge = null;
	let edge = arguments[0];
	this.edge = edge;
}
extend$1(EdgeIntersectionList.prototype, {
	print: function (out) {
		out.println("Intersections:");
		for (var it = this.iterator(); it.hasNext(); ) {
			var ei = it.next();
			ei.print(out);
		}
	},
	iterator: function () {
		return this.nodeMap.values().iterator();
	},
	addSplitEdges: function (edgeList) {
		this.addEndpoints();
		var it = this.iterator();
		var eiPrev = it.next();
		while (it.hasNext()) {
			var ei = it.next();
			var newEdge = this.createSplitEdge(eiPrev, ei);
			edgeList.add(newEdge);
			eiPrev = ei;
		}
	},
	addEndpoints: function () {
		var maxSegIndex = this.edge.pts.length - 1;
		this.add(this.edge.pts[0], 0, 0.0);
		this.add(this.edge.pts[maxSegIndex], maxSegIndex, 0.0);
	},
	createSplitEdge: function (ei0, ei1) {
		var npts = ei1.segmentIndex - ei0.segmentIndex + 2;
		var lastSegStartPt = this.edge.pts[ei1.segmentIndex];
		var useIntPt1 = ei1.dist > 0.0 || !ei1.coord.equals2D(lastSegStartPt);
		if (!useIntPt1) {
			npts--;
		}
		var pts = new Array(npts).fill(null);
		var ipt = 0;
		pts[ipt++] = new Coordinate(ei0.coord);
		for (var i = ei0.segmentIndex + 1; i <= ei1.segmentIndex; i++) {
			pts[ipt++] = this.edge.pts[i];
		}
		if (useIntPt1) pts[ipt] = ei1.coord;
		return new Edge(pts, new Label(this.edge.label));
	},
	add: function (intPt, segmentIndex, dist) {
		var eiNew = new EdgeIntersection(intPt, segmentIndex, dist);
		var ei = this.nodeMap.get(eiNew);
		if (ei !== null) {
			return ei;
		}
		this.nodeMap.put(eiNew, eiNew);
		return eiNew;
	},
	isIntersection: function (pt) {
		for (var it = this.iterator(); it.hasNext(); ) {
			var ei = it.next();
			if (ei.coord.equals(pt)) return true;
		}
		return false;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return EdgeIntersectionList;
	}
});

function Quadrant() {}
extend$1(Quadrant.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Quadrant;
	}
});
Quadrant.isNorthern = function (quad) {
	return quad === Quadrant.NE || quad === Quadrant.NW;
};
Quadrant.isOpposite = function (quad1, quad2) {
	if (quad1 === quad2) return false;
	var diff = (quad1 - quad2 + 4) % 4;
	if (diff === 2) return true;
	return false;
};
Quadrant.commonHalfPlane = function (quad1, quad2) {
	if (quad1 === quad2) return quad1;
	var diff = (quad1 - quad2 + 4) % 4;
	if (diff === 2) return -1;
	var min = quad1 < quad2 ? quad1 : quad2;
	var max = quad1 > quad2 ? quad1 : quad2;
	if (min === 0 && max === 3) return 3;
	return min;
};
Quadrant.isInHalfPlane = function (quad, halfPlane) {
	if (halfPlane === Quadrant.SE) {
		return quad === Quadrant.SE || quad === Quadrant.SW;
	}
	return quad === halfPlane || quad === halfPlane + 1;
};
Quadrant.quadrant = function () {
	if (typeof arguments[0] === "number" && typeof arguments[1] === "number") {
		let dx = arguments[0], dy = arguments[1];
		if (dx === 0.0 && dy === 0.0) throw new IllegalArgumentException("Cannot compute the quadrant for point ( " + dx + ", " + dy + " )");
		if (dx >= 0.0) {
			if (dy >= 0.0) return Quadrant.NE; else return Quadrant.SE;
		} else {
			if (dy >= 0.0) return Quadrant.NW; else return Quadrant.SW;
		}
	} else if (arguments[0] instanceof Coordinate && arguments[1] instanceof Coordinate) {
		let p0 = arguments[0], p1 = arguments[1];
		if (p1.x === p0.x && p1.y === p0.y) throw new IllegalArgumentException("Cannot compute the quadrant for two identical points " + p0);
		if (p1.x >= p0.x) {
			if (p1.y >= p0.y) return Quadrant.NE; else return Quadrant.SE;
		} else {
			if (p1.y >= p0.y) return Quadrant.NW; else return Quadrant.SW;
		}
	}
};
Quadrant.NE = 0;
Quadrant.NW = 1;
Quadrant.SW = 2;
Quadrant.SE = 3;

function MonotoneChainIndexer() {}
extend$1(MonotoneChainIndexer.prototype, {
	getChainStartIndices: function (pts) {
		var start = 0;
		var startIndexList = new ArrayList();
		startIndexList.add(new Integer(start));
		do {
			var last = this.findChainEnd(pts, start);
			startIndexList.add(new Integer(last));
			start = last;
		} while (start < pts.length - 1);
		var startIndex = MonotoneChainIndexer.toIntArray(startIndexList);
		return startIndex;
	},
	findChainEnd: function (pts, start) {
		var chainQuad = Quadrant.quadrant(pts[start], pts[start + 1]);
		var last = start + 1;
		while (last < pts.length) {
			var quad = Quadrant.quadrant(pts[last - 1], pts[last]);
			if (quad !== chainQuad) break;
			last++;
		}
		return last - 1;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return MonotoneChainIndexer;
	}
});
MonotoneChainIndexer.toIntArray = function (list) {
	var array = new Array(list.size()).fill(null);
	for (var i = 0; i < array.length; i++) {
		array[i] = list.get(i).intValue();
	}
	return array;
};

function MonotoneChainEdge() {
	this.e = null;
	this.pts = null;
	this.startIndex = null;
	this.env1 = new Envelope();
	this.env2 = new Envelope();
	let e = arguments[0];
	this.e = e;
	this.pts = e.getCoordinates();
	var mcb = new MonotoneChainIndexer();
	this.startIndex = mcb.getChainStartIndices(this.pts);
}
extend$1(MonotoneChainEdge.prototype, {
	getCoordinates: function () {
		return this.pts;
	},
	getMaxX: function (chainIndex) {
		var x1 = this.pts[this.startIndex[chainIndex]].x;
		var x2 = this.pts[this.startIndex[chainIndex + 1]].x;
		return x1 > x2 ? x1 : x2;
	},
	getMinX: function (chainIndex) {
		var x1 = this.pts[this.startIndex[chainIndex]].x;
		var x2 = this.pts[this.startIndex[chainIndex + 1]].x;
		return x1 < x2 ? x1 : x2;
	},
	computeIntersectsForChain: function () {
		if (arguments.length === 4) {
			let chainIndex0 = arguments[0], mce = arguments[1], chainIndex1 = arguments[2], si = arguments[3];
			this.computeIntersectsForChain(this.startIndex[chainIndex0], this.startIndex[chainIndex0 + 1], mce, mce.startIndex[chainIndex1], mce.startIndex[chainIndex1 + 1], si);
		} else if (arguments.length === 6) {
			let start0 = arguments[0], end0 = arguments[1], mce = arguments[2], start1 = arguments[3], end1 = arguments[4], ei = arguments[5];
			var p00 = this.pts[start0];
			var p01 = this.pts[end0];
			var p10 = mce.pts[start1];
			var p11 = mce.pts[end1];
			if (end0 - start0 === 1 && end1 - start1 === 1) {
				ei.addIntersections(this.e, start0, mce.e, start1);
				return null;
			}
			this.env1.init(p00, p01);
			this.env2.init(p10, p11);
			if (!this.env1.intersects(this.env2)) return null;
			var mid0 = Math.trunc((start0 + end0) / 2);
			var mid1 = Math.trunc((start1 + end1) / 2);
			if (start0 < mid0) {
				if (start1 < mid1) this.computeIntersectsForChain(start0, mid0, mce, start1, mid1, ei);
				if (mid1 < end1) this.computeIntersectsForChain(start0, mid0, mce, mid1, end1, ei);
			}
			if (mid0 < end0) {
				if (start1 < mid1) this.computeIntersectsForChain(mid0, end0, mce, start1, mid1, ei);
				if (mid1 < end1) this.computeIntersectsForChain(mid0, end0, mce, mid1, end1, ei);
			}
		}
	},
	getStartIndexes: function () {
		return this.startIndex;
	},
	computeIntersects: function (mce, si) {
		for (var i = 0; i < this.startIndex.length - 1; i++) {
			for (var j = 0; j < mce.startIndex.length - 1; j++) {
				this.computeIntersectsForChain(i, mce, j, si);
			}
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return MonotoneChainEdge;
	}
});

function Depth() {
	this.depth = Array(2).fill().map(() => Array(3));
	for (var i = 0; i < 2; i++) {
		for (var j = 0; j < 3; j++) {
			this.depth[i][j] = Depth.NULL_VALUE;
		}
	}
}
extend$1(Depth.prototype, {
	getDepth: function (geomIndex, posIndex) {
		return this.depth[geomIndex][posIndex];
	},
	setDepth: function (geomIndex, posIndex, depthValue) {
		this.depth[geomIndex][posIndex] = depthValue;
	},
	isNull: function () {
		if (arguments.length === 0) {
			for (var i = 0; i < 2; i++) {
				for (var j = 0; j < 3; j++) {
					if (this.depth[i][j] !== Depth.NULL_VALUE) return false;
				}
			}
			return true;
		} else if (arguments.length === 1) {
			let geomIndex = arguments[0];
			return this.depth[geomIndex][1] === Depth.NULL_VALUE;
		} else if (arguments.length === 2) {
			let geomIndex = arguments[0], posIndex = arguments[1];
			return this.depth[geomIndex][posIndex] === Depth.NULL_VALUE;
		}
	},
	normalize: function () {
		for (var i = 0; i < 2; i++) {
			if (!this.isNull(i)) {
				var minDepth = this.depth[i][1];
				if (this.depth[i][2] < minDepth) minDepth = this.depth[i][2];
				if (minDepth < 0) minDepth = 0;
				for (var j = 1; j < 3; j++) {
					var newValue = 0;
					if (this.depth[i][j] > minDepth) newValue = 1;
					this.depth[i][j] = newValue;
				}
			}
		}
	},
	getDelta: function (geomIndex) {
		return this.depth[geomIndex][Position.RIGHT] - this.depth[geomIndex][Position.LEFT];
	},
	getLocation: function (geomIndex, posIndex) {
		if (this.depth[geomIndex][posIndex] <= 0) return Location.EXTERIOR;
		return Location.INTERIOR;
	},
	toString: function () {
		return "A: " + this.depth[0][1] + "," + this.depth[0][2] + " B: " + this.depth[1][1] + "," + this.depth[1][2];
	},
	add: function () {
		if (arguments.length === 1) {
			let lbl = arguments[0];
			for (var i = 0; i < 2; i++) {
				for (var j = 1; j < 3; j++) {
					var loc = lbl.getLocation(i, j);
					if (loc === Location.EXTERIOR || loc === Location.INTERIOR) {
						if (this.isNull(i, j)) {
							this.depth[i][j] = Depth.depthAtLocation(loc);
						} else this.depth[i][j] += Depth.depthAtLocation(loc);
					}
				}
			}
		} else if (arguments.length === 3) {
			let geomIndex = arguments[0], posIndex = arguments[1], location = arguments[2];
			if (location === Location.INTERIOR) this.depth[geomIndex][posIndex]++;
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Depth;
	}
});
Depth.depthAtLocation = function (location) {
	if (location === Location.EXTERIOR) return 0;
	if (location === Location.INTERIOR) return 1;
	return Depth.NULL_VALUE;
};
Depth.NULL_VALUE = -1;

function GraphComponent() {
	this.label = null;
	this._isInResult = false;
	this._isCovered = false;
	this._isCoveredSet = false;
	this._isVisited = false;
	if (arguments.length === 0) {} else if (arguments.length === 1) {
		let label = arguments[0];
		this.label = label;
	}
}
extend$1(GraphComponent.prototype, {
	setVisited: function (isVisited) {
		this._isVisited = isVisited;
	},
	setInResult: function (isInResult) {
		this._isInResult = isInResult;
	},
	isCovered: function () {
		return this._isCovered;
	},
	isCoveredSet: function () {
		return this._isCoveredSet;
	},
	setLabel: function (label) {
		this.label = label;
	},
	getLabel: function () {
		return this.label;
	},
	setCovered: function (isCovered) {
		this._isCovered = isCovered;
		this._isCoveredSet = true;
	},
	updateIM: function (im) {
		Assert.isTrue(this.label.getGeometryCount() >= 2, "found partial label");
		this.computeIM(im);
	},
	isInResult: function () {
		return this._isInResult;
	},
	isVisited: function () {
		return this._isVisited;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return GraphComponent;
	}
});

function Edge() {
	GraphComponent.apply(this);
	this.pts = null;
	this.env = null;
	this.eiList = new EdgeIntersectionList(this);
	this.name = null;
	this.mce = null;
	this._isIsolated = true;
	this.depth = new Depth();
	this.depthDelta = 0;
	if (arguments.length === 1) {
		let pts = arguments[0];
		Edge.call(this, pts, null);
	} else if (arguments.length === 2) {
		let pts = arguments[0], label = arguments[1];
		this.pts = pts;
		this.label = label;
	}
}
inherits(Edge, GraphComponent);
extend$1(Edge.prototype, {
	getDepth: function () {
		return this.depth;
	},
	getCollapsedEdge: function () {
		var newPts = new Array(2).fill(null);
		newPts[0] = this.pts[0];
		newPts[1] = this.pts[1];
		var newe = new Edge(newPts, Label.toLineLabel(this.label));
		return newe;
	},
	isIsolated: function () {
		return this._isIsolated;
	},
	getCoordinates: function () {
		return this.pts;
	},
	setIsolated: function (isIsolated) {
		this._isIsolated = isIsolated;
	},
	setName: function (name) {
		this.name = name;
	},
	equals: function (o) {
		if (!(o instanceof Edge)) return false;
		var e = o;
		if (this.pts.length !== e.pts.length) return false;
		var isEqualForward = true;
		var isEqualReverse = true;
		var iRev = this.pts.length;
		for (var i = 0; i < this.pts.length; i++) {
			if (!this.pts[i].equals2D(e.pts[i])) {
				isEqualForward = false;
			}
			if (!this.pts[i].equals2D(e.pts[-- iRev])) {
				isEqualReverse = false;
			}
			if (!isEqualForward && !isEqualReverse) return false;
		}
		return true;
	},
	getCoordinate: function () {
		if (arguments.length === 0) {
			if (this.pts.length > 0) return this.pts[0];
			return null;
		} else if (arguments.length === 1) {
			let i = arguments[0];
			return this.pts[i];
		}
	},
	print: function (out) {
		out.print("edge " + this.name + ": ");
		out.print("LINESTRING (");
		for (var i = 0; i < this.pts.length; i++) {
			if (i > 0) out.print(",");
			out.print(this.pts[i].x + " " + this.pts[i].y);
		}
		out.print(")  " + this.label + " " + this.depthDelta);
	},
	computeIM: function (im) {
		Edge.updateIM(this.label, im);
	},
	isCollapsed: function () {
		if (!this.label.isArea()) return false;
		if (this.pts.length !== 3) return false;
		if (this.pts[0].equals(this.pts[2])) return true;
		return false;
	},
	isClosed: function () {
		return this.pts[0].equals(this.pts[this.pts.length - 1]);
	},
	getMaximumSegmentIndex: function () {
		return this.pts.length - 1;
	},
	getDepthDelta: function () {
		return this.depthDelta;
	},
	getNumPoints: function () {
		return this.pts.length;
	},
	printReverse: function (out) {
		out.print("edge " + this.name + ": ");
		for (var i = this.pts.length - 1; i >= 0; i--) {
			out.print(this.pts[i] + " ");
		}
		out.println("");
	},
	getMonotoneChainEdge: function () {
		if (this.mce === null) this.mce = new MonotoneChainEdge(this);
		return this.mce;
	},
	getEnvelope: function () {
		if (this.env === null) {
			this.env = new Envelope();
			for (var i = 0; i < this.pts.length; i++) {
				this.env.expandToInclude(this.pts[i]);
			}
		}
		return this.env;
	},
	addIntersection: function (li, segmentIndex, geomIndex, intIndex) {
		var intPt = new Coordinate(li.getIntersection(intIndex));
		var normalizedSegmentIndex = segmentIndex;
		var dist = li.getEdgeDistance(geomIndex, intIndex);
		var nextSegIndex = normalizedSegmentIndex + 1;
		if (nextSegIndex < this.pts.length) {
			var nextPt = this.pts[nextSegIndex];
			if (intPt.equals2D(nextPt)) {
				normalizedSegmentIndex = nextSegIndex;
				dist = 0.0;
			}
		}
		var ei = this.eiList.add(intPt, normalizedSegmentIndex, dist);
	},
	toString: function () {
		var buf = new StringBuffer();
		buf.append("edge " + this.name + ": ");
		buf.append("LINESTRING (");
		for (var i = 0; i < this.pts.length; i++) {
			if (i > 0) buf.append(",");
			buf.append(this.pts[i].x + " " + this.pts[i].y);
		}
		buf.append(")  " + this.label + " " + this.depthDelta);
		return buf.toString();
	},
	isPointwiseEqual: function (e) {
		if (this.pts.length !== e.pts.length) return false;
		for (var i = 0; i < this.pts.length; i++) {
			if (!this.pts[i].equals2D(e.pts[i])) {
				return false;
			}
		}
		return true;
	},
	setDepthDelta: function (depthDelta) {
		this.depthDelta = depthDelta;
	},
	getEdgeIntersectionList: function () {
		return this.eiList;
	},
	addIntersections: function (li, segmentIndex, geomIndex) {
		for (var i = 0; i < li.getIntersectionNum(); i++) {
			this.addIntersection(li, segmentIndex, geomIndex, i);
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Edge;
	}
});
Edge.updateIM = function () {
	if (arguments.length === 2) {
		let label = arguments[0], im = arguments[1];
		im.setAtLeastIfValid(label.getLocation(0, Position.ON), label.getLocation(1, Position.ON), 1);
		if (label.isArea()) {
			im.setAtLeastIfValid(label.getLocation(0, Position.LEFT), label.getLocation(1, Position.LEFT), 2);
			im.setAtLeastIfValid(label.getLocation(0, Position.RIGHT), label.getLocation(1, Position.RIGHT), 2);
		}
	} else return GraphComponent.prototype.updateIM.apply(this, arguments);
};

function Node() {
	GraphComponent.apply(this);
	this.coord = null;
	this.edges = null;
	let coord = arguments[0], edges = arguments[1];
	this.coord = coord;
	this.edges = edges;
	this.label = new Label(0, Location.NONE);
}
inherits(Node, GraphComponent);
extend$1(Node.prototype, {
	isIncidentEdgeInResult: function () {
		for (var it = this.getEdges().getEdges().iterator(); it.hasNext(); ) {
			var de = it.next();
			if (de.getEdge().isInResult()) return true;
		}
		return false;
	},
	isIsolated: function () {
		return this.label.getGeometryCount() === 1;
	},
	getCoordinate: function () {
		return this.coord;
	},
	print: function (out) {
		out.println("node " + this.coord + " lbl: " + this.label);
	},
	computeIM: function (im) {},
	computeMergedLocation: function (label2, eltIndex) {
		var loc = Location.NONE;
		loc = this.label.getLocation(eltIndex);
		if (!label2.isNull(eltIndex)) {
			var nLoc = label2.getLocation(eltIndex);
			if (loc !== Location.BOUNDARY) loc = nLoc;
		}
		return loc;
	},
	setLabel: function () {
		if (arguments.length === 2) {
			let argIndex = arguments[0], onLocation = arguments[1];
			if (this.label === null) {
				this.label = new Label(argIndex, onLocation);
			} else this.label.setLocation(argIndex, onLocation);
		} else return GraphComponent.prototype.setLabel.apply(this, arguments);
	},
	getEdges: function () {
		return this.edges;
	},
	mergeLabel: function () {
		if (arguments[0] instanceof Node) {
			let n = arguments[0];
			this.mergeLabel(n.label);
		} else if (arguments[0] instanceof Label) {
			let label2 = arguments[0];
			for (var i = 0; i < 2; i++) {
				var loc = this.computeMergedLocation(label2, i);
				var thisLoc = this.label.getLocation(i);
				if (thisLoc === Location.NONE) this.label.setLocation(i, loc);
			}
		}
	},
	add: function (e) {
		this.edges.insert(e);
		e.setNode(this);
	},
	setLabelBoundary: function (argIndex) {
		if (this.label === null) return null;
		var loc = Location.NONE;
		if (this.label !== null) loc = this.label.getLocation(argIndex);
		var newLoc = null;
		switch (loc) {
			case Location.BOUNDARY:
				newLoc = Location.INTERIOR;
				break;
			case Location.INTERIOR:
				newLoc = Location.BOUNDARY;
				break;
			default:
				newLoc = Location.BOUNDARY;
				break;
		}
		this.label.setLocation(argIndex, newLoc);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Node;
	}
});

function NodeMap() {
	this.nodeMap = new TreeMap();
	this.nodeFact = null;
	let nodeFact = arguments[0];
	this.nodeFact = nodeFact;
}
extend$1(NodeMap.prototype, {
	find: function (coord) {
		return this.nodeMap.get(coord);
	},
	addNode: function () {
		if (arguments[0] instanceof Coordinate) {
			let coord = arguments[0];
			var node = this.nodeMap.get(coord);
			if (node === null) {
				node = this.nodeFact.createNode(coord);
				this.nodeMap.put(coord, node);
			}
			return node;
		} else if (arguments[0] instanceof Node) {
			let n = arguments[0];
			var node = this.nodeMap.get(n.getCoordinate());
			if (node === null) {
				this.nodeMap.put(n.getCoordinate(), n);
				return n;
			}
			node.mergeLabel(n);
			return node;
		}
	},
	print: function (out) {
		for (var it = this.iterator(); it.hasNext(); ) {
			var n = it.next();
			n.print(out);
		}
	},
	iterator: function () {
		return this.nodeMap.values().iterator();
	},
	values: function () {
		return this.nodeMap.values();
	},
	getBoundaryNodes: function (geomIndex) {
		var bdyNodes = new ArrayList();
		for (var i = this.iterator(); i.hasNext(); ) {
			var node = i.next();
			if (node.getLabel().getLocation(geomIndex) === Location.BOUNDARY) bdyNodes.add(node);
		}
		return bdyNodes;
	},
	add: function (e) {
		var p = e.getCoordinate();
		var n = this.addNode(p);
		n.add(e);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return NodeMap;
	}
});

function EdgeEnd() {
	this.edge = null;
	this.label = null;
	this.node = null;
	this.p0 = null;
	this.p1 = null;
	this.dx = null;
	this.dy = null;
	this.quadrant = null;
	if (arguments.length === 1) {
		let edge = arguments[0];
		this.edge = edge;
	} else if (arguments.length === 3) {
		let edge = arguments[0], p0 = arguments[1], p1 = arguments[2];
		EdgeEnd.call(this, edge, p0, p1, null);
	} else if (arguments.length === 4) {
		let edge = arguments[0], p0 = arguments[1], p1 = arguments[2], label = arguments[3];
		EdgeEnd.call(this, edge);
		this.init(p0, p1);
		this.label = label;
	}
}
extend$1(EdgeEnd.prototype, {
	compareDirection: function (e) {
		if (this.dx === e.dx && this.dy === e.dy) return 0;
		if (this.quadrant > e.quadrant) return 1;
		if (this.quadrant < e.quadrant) return -1;
		return CGAlgorithms.computeOrientation(e.p0, e.p1, this.p1);
	},
	getDy: function () {
		return this.dy;
	},
	getCoordinate: function () {
		return this.p0;
	},
	setNode: function (node) {
		this.node = node;
	},
	print: function (out) {
		var angle = Math.atan2(this.dy, this.dx);
		var className = this.getClass().getName();
		var lastDotPos = className.lastIndexOf('.');
		var name = className.substring(lastDotPos + 1);
		out.print("  " + name + ": " + this.p0 + " - " + this.p1 + " " + this.quadrant + ":" + angle + "   " + this.label);
	},
	compareTo: function (obj) {
		var e = obj;
		return this.compareDirection(e);
	},
	getDirectedCoordinate: function () {
		return this.p1;
	},
	getDx: function () {
		return this.dx;
	},
	getLabel: function () {
		return this.label;
	},
	getEdge: function () {
		return this.edge;
	},
	getQuadrant: function () {
		return this.quadrant;
	},
	getNode: function () {
		return this.node;
	},
	toString: function () {
		var angle = Math.atan2(this.dy, this.dx);
		var className = this.getClass().getName();
		var lastDotPos = className.lastIndexOf('.');
		var name = className.substring(lastDotPos + 1);
		return "  " + name + ": " + this.p0 + " - " + this.p1 + " " + this.quadrant + ":" + angle + "   " + this.label;
	},
	computeLabel: function (boundaryNodeRule) {},
	init: function (p0, p1) {
		this.p0 = p0;
		this.p1 = p1;
		this.dx = p1.x - p0.x;
		this.dy = p1.y - p0.y;
		this.quadrant = Quadrant.quadrant(this.dx, this.dy);
		Assert.isTrue(!(this.dx === 0 && this.dy === 0), "EdgeEnd with identical endpoints found");
	},
	interfaces_: function () {
		return [Comparable];
	},
	getClass: function () {
		return EdgeEnd;
	}
});

function TopologyException() {
	this.pt = null;
	if (arguments.length === 1) {
		let msg = arguments[0];
		RuntimeException.call(this, msg);
	} else if (arguments.length === 2) {
		let msg = arguments[0], pt = arguments[1];
		RuntimeException.call(this, TopologyException.msgWithCoord(msg, pt));
		this.name = 'TopologyException';
		this.pt = new Coordinate(pt);
	}
}
inherits(TopologyException, RuntimeException);
extend$1(TopologyException.prototype, {
	getCoordinate: function () {
		return this.pt;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return TopologyException;
	}
});
TopologyException.msgWithCoord = function (msg, pt) {
	if (pt !== null) return msg + " [ " + pt + " ]";
	return msg;
};

function DirectedEdge() {
	this._isForward = null;
	this._isInResult = false;
	this._isVisited = false;
	this.sym = null;
	this.next = null;
	this.nextMin = null;
	this.edgeRing = null;
	this.minEdgeRing = null;
	this.depth = [0, -999, -999];
	let edge = arguments[0], isForward = arguments[1];
	EdgeEnd.call(this, edge);
	this._isForward = isForward;
	if (isForward) {
		this.init(edge.getCoordinate(0), edge.getCoordinate(1));
	} else {
		var n = edge.getNumPoints() - 1;
		this.init(edge.getCoordinate(n), edge.getCoordinate(n - 1));
	}
	this.computeDirectedLabel();
}
inherits(DirectedEdge, EdgeEnd);
extend$1(DirectedEdge.prototype, {
	getNextMin: function () {
		return this.nextMin;
	},
	getDepth: function (position) {
		return this.depth[position];
	},
	setVisited: function (isVisited) {
		this._isVisited = isVisited;
	},
	computeDirectedLabel: function () {
		this.label = new Label(this.edge.getLabel());
		if (!this._isForward) this.label.flip();
	},
	getNext: function () {
		return this.next;
	},
	setDepth: function (position, depthVal) {
		if (this.depth[position] !== -999) {
			if (this.depth[position] !== depthVal) throw new TopologyException("assigned depths do not match", this.getCoordinate());
		}
		this.depth[position] = depthVal;
	},
	isInteriorAreaEdge: function () {
		var isInteriorAreaEdge = true;
		for (var i = 0; i < 2; i++) {
			if (!(this.label.isArea(i) && this.label.getLocation(i, Position.LEFT) === Location.INTERIOR && this.label.getLocation(i, Position.RIGHT) === Location.INTERIOR)) {
				isInteriorAreaEdge = false;
			}
		}
		return isInteriorAreaEdge;
	},
	setNextMin: function (nextMin) {
		this.nextMin = nextMin;
	},
	print: function (out) {
		EdgeEnd.prototype.print.call(this, out);
		out.print(" " + this.depth[Position.LEFT] + "/" + this.depth[Position.RIGHT]);
		out.print(" (" + this.getDepthDelta() + ")");
		if (this._isInResult) out.print(" inResult");
	},
	setMinEdgeRing: function (minEdgeRing) {
		this.minEdgeRing = minEdgeRing;
	},
	isLineEdge: function () {
		var isLine = this.label.isLine(0) || this.label.isLine(1);
		var isExteriorIfArea0 = !this.label.isArea(0) || this.label.allPositionsEqual(0, Location.EXTERIOR);
		var isExteriorIfArea1 = !this.label.isArea(1) || this.label.allPositionsEqual(1, Location.EXTERIOR);
		return isLine && isExteriorIfArea0 && isExteriorIfArea1;
	},
	setEdgeRing: function (edgeRing) {
		this.edgeRing = edgeRing;
	},
	getMinEdgeRing: function () {
		return this.minEdgeRing;
	},
	getDepthDelta: function () {
		var depthDelta = this.edge.getDepthDelta();
		if (!this._isForward) depthDelta = -depthDelta;
		return depthDelta;
	},
	setInResult: function (isInResult) {
		this._isInResult = isInResult;
	},
	getSym: function () {
		return this.sym;
	},
	isForward: function () {
		return this._isForward;
	},
	getEdge: function () {
		return this.edge;
	},
	printEdge: function (out) {
		this.print(out);
		out.print(" ");
		if (this._isForward) this.edge.print(out); else this.edge.printReverse(out);
	},
	setSym: function (de) {
		this.sym = de;
	},
	setVisitedEdge: function (isVisited) {
		this.setVisited(isVisited);
		this.sym.setVisited(isVisited);
	},
	setEdgeDepths: function (position, depth) {
		var depthDelta = this.getEdge().getDepthDelta();
		if (!this._isForward) depthDelta = -depthDelta;
		var directionFactor = 1;
		if (position === Position.LEFT) directionFactor = -1;
		var oppositePos = Position.opposite(position);
		var delta = depthDelta * directionFactor;
		var oppositeDepth = depth + delta;
		this.setDepth(position, depth);
		this.setDepth(oppositePos, oppositeDepth);
	},
	getEdgeRing: function () {
		return this.edgeRing;
	},
	isInResult: function () {
		return this._isInResult;
	},
	setNext: function (next) {
		this.next = next;
	},
	isVisited: function () {
		return this._isVisited;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return DirectedEdge;
	}
});
DirectedEdge.depthFactor = function (currLocation, nextLocation) {
	if (currLocation === Location.EXTERIOR && nextLocation === Location.INTERIOR) return 1; else if (currLocation === Location.INTERIOR && nextLocation === Location.EXTERIOR) return -1;
	return 0;
};

function NodeFactory() {}
extend$1(NodeFactory.prototype, {
	createNode: function (coord) {
		return new Node(coord, null);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return NodeFactory;
	}
});

function PlanarGraph() {
	this.edges = new ArrayList();
	this.nodes = null;
	this.edgeEndList = new ArrayList();
	if (arguments.length === 0) {
		this.nodes = new NodeMap(new NodeFactory());
	} else if (arguments.length === 1) {
		let nodeFact = arguments[0];
		this.nodes = new NodeMap(nodeFact);
	}
}
extend$1(PlanarGraph.prototype, {
	printEdges: function (out) {
		out.println("Edges:");
		for (var i = 0; i < this.edges.size(); i++) {
			out.println("edge " + i + ":");
			var e = this.edges.get(i);
			e.print(out);
			e.eiList.print(out);
		}
	},
	find: function (coord) {
		return this.nodes.find(coord);
	},
	addNode: function () {
		if (arguments[0] instanceof Node) {
			let node = arguments[0];
			return this.nodes.addNode(node);
		} else if (arguments[0] instanceof Coordinate) {
			let coord = arguments[0];
			return this.nodes.addNode(coord);
		}
	},
	getNodeIterator: function () {
		return this.nodes.iterator();
	},
	linkResultDirectedEdges: function () {
		for (var nodeit = this.nodes.iterator(); nodeit.hasNext(); ) {
			var node = nodeit.next();
			node.getEdges().linkResultDirectedEdges();
		}
	},
	debugPrintln: function (o) {
		System.out.println(o);
	},
	isBoundaryNode: function (geomIndex, coord) {
		var node = this.nodes.find(coord);
		if (node === null) return false;
		var label = node.getLabel();
		if (label !== null && label.getLocation(geomIndex) === Location.BOUNDARY) return true;
		return false;
	},
	linkAllDirectedEdges: function () {
		for (var nodeit = this.nodes.iterator(); nodeit.hasNext(); ) {
			var node = nodeit.next();
			node.getEdges().linkAllDirectedEdges();
		}
	},
	matchInSameDirection: function (p0, p1, ep0, ep1) {
		if (!p0.equals(ep0)) return false;
		if (CGAlgorithms.computeOrientation(p0, p1, ep1) === CGAlgorithms.COLLINEAR && Quadrant.quadrant(p0, p1) === Quadrant.quadrant(ep0, ep1)) return true;
		return false;
	},
	getEdgeEnds: function () {
		return this.edgeEndList;
	},
	debugPrint: function (o) {
		System.out.print(o);
	},
	getEdgeIterator: function () {
		return this.edges.iterator();
	},
	findEdgeInSameDirection: function (p0, p1) {
		for (var i = 0; i < this.edges.size(); i++) {
			var e = this.edges.get(i);
			var eCoord = e.getCoordinates();
			if (this.matchInSameDirection(p0, p1, eCoord[0], eCoord[1])) return e;
			if (this.matchInSameDirection(p0, p1, eCoord[eCoord.length - 1], eCoord[eCoord.length - 2])) return e;
		}
		return null;
	},
	insertEdge: function (e) {
		this.edges.add(e);
	},
	findEdgeEnd: function (e) {
		for (var i = this.getEdgeEnds().iterator(); i.hasNext(); ) {
			var ee = i.next();
			if (ee.getEdge() === e) return ee;
		}
		return null;
	},
	addEdges: function (edgesToAdd) {
		for (var it = edgesToAdd.iterator(); it.hasNext(); ) {
			var e = it.next();
			this.edges.add(e);
			var de1 = new DirectedEdge(e, true);
			var de2 = new DirectedEdge(e, false);
			de1.setSym(de2);
			de2.setSym(de1);
			this.add(de1);
			this.add(de2);
		}
	},
	add: function (e) {
		this.nodes.add(e);
		this.edgeEndList.add(e);
	},
	getNodes: function () {
		return this.nodes.values();
	},
	findEdge: function (p0, p1) {
		for (var i = 0; i < this.edges.size(); i++) {
			var e = this.edges.get(i);
			var eCoord = e.getCoordinates();
			if (p0.equals(eCoord[0]) && p1.equals(eCoord[1])) return e;
		}
		return null;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return PlanarGraph;
	}
});
PlanarGraph.linkResultDirectedEdges = function (nodes) {
	for (var nodeit = nodes.iterator(); nodeit.hasNext(); ) {
		var node = nodeit.next();
		node.getEdges().linkResultDirectedEdges();
	}
};

function GeometryGraph() {
	PlanarGraph.apply(this);
	this.parentGeom = null;
	this.lineEdgeMap = new HashMap();
	this.boundaryNodeRule = null;
	this.useBoundaryDeterminationRule = true;
	this.argIndex = null;
	this.boundaryNodes = null;
	this._hasTooFewPoints = false;
	this.invalidPoint = null;
	this.areaPtLocator = null;
	this.ptLocator = new PointLocator();
	if (arguments.length === 2) {
		let argIndex = arguments[0], parentGeom = arguments[1];
		GeometryGraph.call(this, argIndex, parentGeom, BoundaryNodeRule.OGC_SFS_BOUNDARY_RULE);
	} else if (arguments.length === 3) {
		let argIndex = arguments[0], parentGeom = arguments[1], boundaryNodeRule = arguments[2];
		this.argIndex = argIndex;
		this.parentGeom = parentGeom;
		this.boundaryNodeRule = boundaryNodeRule;
		if (parentGeom !== null) {
			this.add(parentGeom);
		}
	}
}
inherits(GeometryGraph, PlanarGraph);
extend$1(GeometryGraph.prototype, {
	insertBoundaryPoint: function (argIndex, coord) {
		var n = this.nodes.addNode(coord);
		var lbl = n.getLabel();
		var boundaryCount = 1;
		var loc = Location.NONE;
		loc = lbl.getLocation(argIndex, Position.ON);
		if (loc === Location.BOUNDARY) boundaryCount++;
		var newLoc = GeometryGraph.determineBoundary(this.boundaryNodeRule, boundaryCount);
		lbl.setLocation(argIndex, newLoc);
	},
	computeSelfNodes: function () {
		if (arguments.length === 2) {
			let li = arguments[0], computeRingSelfNodes = arguments[1];
			return this.computeSelfNodes(li, computeRingSelfNodes, false);
		} else if (arguments.length === 3) {
			let li = arguments[0], computeRingSelfNodes = arguments[1], isDoneIfProperInt = arguments[2];
			var si = new SegmentIntersector(li, true, false);
			si.setIsDoneIfProperInt(isDoneIfProperInt);
			var esi = this.createEdgeSetIntersector();
			var isRings = this.parentGeom instanceof LinearRing || this.parentGeom instanceof Polygon || this.parentGeom instanceof MultiPolygon;
			var computeAllSegments = computeRingSelfNodes || !isRings;
			esi.computeIntersections(this.edges, si, computeAllSegments);
			this.addSelfIntersectionNodes(this.argIndex);
			return si;
		}
	},
	computeSplitEdges: function (edgelist) {
		for (var i = this.edges.iterator(); i.hasNext(); ) {
			var e = i.next();
			e.eiList.addSplitEdges(edgelist);
		}
	},
	computeEdgeIntersections: function (g, li, includeProper) {
		var si = new SegmentIntersector(li, includeProper, true);
		si.setBoundaryNodes(this.getBoundaryNodes(), g.getBoundaryNodes());
		var esi = this.createEdgeSetIntersector();
		esi.computeIntersections(this.edges, g.edges, si);
		return si;
	},
	getGeometry: function () {
		return this.parentGeom;
	},
	getBoundaryNodeRule: function () {
		return this.boundaryNodeRule;
	},
	hasTooFewPoints: function () {
		return this._hasTooFewPoints;
	},
	addPoint: function () {
		if (arguments[0] instanceof Point) {
			let p = arguments[0];
			var coord = p.getCoordinate();
			this.insertPoint(this.argIndex, coord, Location.INTERIOR);
		} else if (arguments[0] instanceof Coordinate) {
			let pt = arguments[0];
			this.insertPoint(this.argIndex, pt, Location.INTERIOR);
		}
	},
	addPolygon: function (p) {
		this.addPolygonRing(p.getExteriorRing(), Location.EXTERIOR, Location.INTERIOR);
		for (var i = 0; i < p.getNumInteriorRing(); i++) {
			var hole = p.getInteriorRingN(i);
			this.addPolygonRing(hole, Location.INTERIOR, Location.EXTERIOR);
		}
	},
	addEdge: function (e) {
		this.insertEdge(e);
		var coord = e.getCoordinates();
		this.insertPoint(this.argIndex, coord[0], Location.BOUNDARY);
		this.insertPoint(this.argIndex, coord[coord.length - 1], Location.BOUNDARY);
	},
	addLineString: function (line) {
		var coord = CoordinateArrays.removeRepeatedPoints(line.getCoordinates());
		if (coord.length < 2) {
			this._hasTooFewPoints = true;
			this.invalidPoint = coord[0];
			return null;
		}
		var e = new Edge(coord, new Label(this.argIndex, Location.INTERIOR));
		this.lineEdgeMap.put(line, e);
		this.insertEdge(e);
		Assert.isTrue(coord.length >= 2, "found LineString with single point");
		this.insertBoundaryPoint(this.argIndex, coord[0]);
		this.insertBoundaryPoint(this.argIndex, coord[coord.length - 1]);
	},
	getInvalidPoint: function () {
		return this.invalidPoint;
	},
	getBoundaryPoints: function () {
		var coll = this.getBoundaryNodes();
		var pts = new Array(coll.size()).fill(null);
		var i = 0;
		for (var it = coll.iterator(); it.hasNext(); ) {
			var node = it.next();
			pts[i++] = node.getCoordinate().copy();
		}
		return pts;
	},
	getBoundaryNodes: function () {
		if (this.boundaryNodes === null) this.boundaryNodes = this.nodes.getBoundaryNodes(this.argIndex);
		return this.boundaryNodes;
	},
	addSelfIntersectionNode: function (argIndex, coord, loc) {
		if (this.isBoundaryNode(argIndex, coord)) return null;
		if (loc === Location.BOUNDARY && this.useBoundaryDeterminationRule) this.insertBoundaryPoint(argIndex, coord); else this.insertPoint(argIndex, coord, loc);
	},
	addPolygonRing: function (lr, cwLeft, cwRight) {
		if (lr.isEmpty()) return null;
		var coord = CoordinateArrays.removeRepeatedPoints(lr.getCoordinates());
		if (coord.length < 4) {
			this._hasTooFewPoints = true;
			this.invalidPoint = coord[0];
			return null;
		}
		var left = cwLeft;
		var right = cwRight;
		if (CGAlgorithms.isCCW(coord)) {
			left = cwRight;
			right = cwLeft;
		}
		var e = new Edge(coord, new Label(this.argIndex, Location.BOUNDARY, left, right));
		this.lineEdgeMap.put(lr, e);
		this.insertEdge(e);
		this.insertPoint(this.argIndex, coord[0], Location.BOUNDARY);
	},
	insertPoint: function (argIndex, coord, onLocation) {
		var n = this.nodes.addNode(coord);
		var lbl = n.getLabel();
		if (lbl === null) {
			n.label = new Label(argIndex, onLocation);
		} else lbl.setLocation(argIndex, onLocation);
	},
	createEdgeSetIntersector: function () {
		return new SimpleMCSweepLineIntersector();
	},
	addSelfIntersectionNodes: function (argIndex) {
		for (var i = this.edges.iterator(); i.hasNext(); ) {
			var e = i.next();
			var eLoc = e.getLabel().getLocation(argIndex);
			for (var eiIt = e.eiList.iterator(); eiIt.hasNext(); ) {
				var ei = eiIt.next();
				this.addSelfIntersectionNode(argIndex, ei.coord, eLoc);
			}
		}
	},
	add: function () {
		if (arguments.length === 1) {
			let g = arguments[0];
			if (g.isEmpty()) return null;
			if (g instanceof MultiPolygon) this.useBoundaryDeterminationRule = false;
			if (g instanceof Polygon) this.addPolygon(g); else if (g instanceof LineString) this.addLineString(g); else if (g instanceof Point) this.addPoint(g); else if (g instanceof MultiPoint) this.addCollection(g); else if (g instanceof MultiLineString) this.addCollection(g); else if (g instanceof MultiPolygon) this.addCollection(g); else if (g instanceof GeometryCollection) this.addCollection(g); else throw new UnsupportedOperationException(g.getClass().getName());
		} else return PlanarGraph.prototype.add.apply(this, arguments);
	},
	addCollection: function (gc) {
		for (var i = 0; i < gc.getNumGeometries(); i++) {
			var g = gc.getGeometryN(i);
			this.add(g);
		}
	},
	locate: function (pt) {
		if (hasInterface(this.parentGeom, Polygonal) && this.parentGeom.getNumGeometries() > 50) {
			if (this.areaPtLocator === null) {
				this.areaPtLocator = new IndexedPointInAreaLocator(this.parentGeom);
			}
			return this.areaPtLocator.locate(pt);
		}
		return this.ptLocator.locate(pt, this.parentGeom);
	},
	findEdge: function () {
		if (arguments.length === 1) {
			let line = arguments[0];
			return this.lineEdgeMap.get(line);
		} else return PlanarGraph.prototype.findEdge.apply(this, arguments);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return GeometryGraph;
	}
});
GeometryGraph.determineBoundary = function (boundaryNodeRule, boundaryCount) {
	return boundaryNodeRule.isInBoundary(boundaryCount) ? Location.BOUNDARY : Location.INTERIOR;
};

function IsSimpleOp() {
	this.inputGeom = null;
	this.isClosedEndpointsInInterior = true;
	this.nonSimpleLocation = null;
	if (arguments.length === 1) {
		let geom = arguments[0];
		this.inputGeom = geom;
	} else if (arguments.length === 2) {
		let geom = arguments[0], boundaryNodeRule = arguments[1];
		this.inputGeom = geom;
		this.isClosedEndpointsInInterior = !boundaryNodeRule.isInBoundary(2);
	}
}
extend$1(IsSimpleOp.prototype, {
	isSimpleMultiPoint: function (mp) {
		if (mp.isEmpty()) return true;
		var points = new TreeSet();
		for (var i = 0; i < mp.getNumGeometries(); i++) {
			var pt = mp.getGeometryN(i);
			var p = pt.getCoordinate();
			if (points.contains(p)) {
				this.nonSimpleLocation = p;
				return false;
			}
			points.add(p);
		}
		return true;
	},
	isSimplePolygonal: function (geom) {
		var rings = LinearComponentExtracter.getLines(geom);
		for (var i = rings.iterator(); i.hasNext(); ) {
			var ring = i.next();
			if (!this.isSimpleLinearGeometry(ring)) return false;
		}
		return true;
	},
	hasClosedEndpointIntersection: function (graph) {
		var endPoints = new TreeMap();
		for (var i = graph.getEdgeIterator(); i.hasNext(); ) {
			var e = i.next();
			var maxSegmentIndex = e.getMaximumSegmentIndex();
			var isClosed = e.isClosed();
			var p0 = e.getCoordinate(0);
			this.addEndpoint(endPoints, p0, isClosed);
			var p1 = e.getCoordinate(e.getNumPoints() - 1);
			this.addEndpoint(endPoints, p1, isClosed);
		}
		for (var i = endPoints.values().iterator(); i.hasNext(); ) {
			var eiInfo = i.next();
			if (eiInfo.isClosed && eiInfo.degree !== 2) {
				this.nonSimpleLocation = eiInfo.getCoordinate();
				return true;
			}
		}
		return false;
	},
	getNonSimpleLocation: function () {
		return this.nonSimpleLocation;
	},
	isSimpleLinearGeometry: function (geom) {
		if (geom.isEmpty()) return true;
		var graph = new GeometryGraph(0, geom);
		var li = new RobustLineIntersector();
		var si = graph.computeSelfNodes(li, true);
		if (!si.hasIntersection()) return true;
		if (si.hasProperIntersection()) {
			this.nonSimpleLocation = si.getProperIntersectionPoint();
			return false;
		}
		if (this.hasNonEndpointIntersection(graph)) return false;
		if (this.isClosedEndpointsInInterior) {
			if (this.hasClosedEndpointIntersection(graph)) return false;
		}
		return true;
	},
	hasNonEndpointIntersection: function (graph) {
		for (var i = graph.getEdgeIterator(); i.hasNext(); ) {
			var e = i.next();
			var maxSegmentIndex = e.getMaximumSegmentIndex();
			for (var eiIt = e.getEdgeIntersectionList().iterator(); eiIt.hasNext(); ) {
				var ei = eiIt.next();
				if (!ei.isEndPoint(maxSegmentIndex)) {
					this.nonSimpleLocation = ei.getCoordinate();
					return true;
				}
			}
		}
		return false;
	},
	addEndpoint: function (endPoints, p, isClosed) {
		var eiInfo = endPoints.get(p);
		if (eiInfo === null) {
			eiInfo = new EndpointInfo(p);
			endPoints.put(p, eiInfo);
		}
		eiInfo.addEndpoint(isClosed);
	},
	computeSimple: function (geom) {
		this.nonSimpleLocation = null;
		if (geom.isEmpty()) return true;
		if (geom instanceof LineString) return this.isSimpleLinearGeometry(geom);
		if (geom instanceof MultiLineString) return this.isSimpleLinearGeometry(geom);
		if (geom instanceof MultiPoint) return this.isSimpleMultiPoint(geom);
		if (hasInterface(geom, Polygonal)) return this.isSimplePolygonal(geom);
		if (geom instanceof GeometryCollection) return this.isSimpleGeometryCollection(geom);
		return true;
	},
	isSimple: function () {
		this.nonSimpleLocation = null;
		return this.computeSimple(this.inputGeom);
	},
	isSimpleGeometryCollection: function (geom) {
		for (var i = 0; i < geom.getNumGeometries(); i++) {
			var comp = geom.getGeometryN(i);
			if (!this.computeSimple(comp)) return false;
		}
		return true;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return IsSimpleOp;
	}
});
function EndpointInfo() {
	this.pt = null;
	this.isClosed = null;
	this.degree = null;
	let pt = arguments[0];
	this.pt = pt;
	this.isClosed = false;
	this.degree = 0;
}
extend$1(EndpointInfo.prototype, {
	addEndpoint: function (isClosed) {
		this.degree++;
		this.isClosed |= isClosed;
	},
	getCoordinate: function () {
		return this.pt;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return EndpointInfo;
	}
});
IsSimpleOp.EndpointInfo = EndpointInfo;

function IntersectionMatrix() {
	this.matrix = null;
	if (arguments.length === 0) {
		this.matrix = Array(3).fill().map(() => Array(3));
		this.setAll(Dimension.FALSE);
	} else if (arguments.length === 1) {
		if (typeof arguments[0] === "string") {
			let elements = arguments[0];
			IntersectionMatrix.call(this);
			this.set(elements);
		} else if (arguments[0] instanceof IntersectionMatrix) {
			let other = arguments[0];
			IntersectionMatrix.call(this);
			this.matrix[Location.INTERIOR][Location.INTERIOR] = other.matrix[Location.INTERIOR][Location.INTERIOR];
			this.matrix[Location.INTERIOR][Location.BOUNDARY] = other.matrix[Location.INTERIOR][Location.BOUNDARY];
			this.matrix[Location.INTERIOR][Location.EXTERIOR] = other.matrix[Location.INTERIOR][Location.EXTERIOR];
			this.matrix[Location.BOUNDARY][Location.INTERIOR] = other.matrix[Location.BOUNDARY][Location.INTERIOR];
			this.matrix[Location.BOUNDARY][Location.BOUNDARY] = other.matrix[Location.BOUNDARY][Location.BOUNDARY];
			this.matrix[Location.BOUNDARY][Location.EXTERIOR] = other.matrix[Location.BOUNDARY][Location.EXTERIOR];
			this.matrix[Location.EXTERIOR][Location.INTERIOR] = other.matrix[Location.EXTERIOR][Location.INTERIOR];
			this.matrix[Location.EXTERIOR][Location.BOUNDARY] = other.matrix[Location.EXTERIOR][Location.BOUNDARY];
			this.matrix[Location.EXTERIOR][Location.EXTERIOR] = other.matrix[Location.EXTERIOR][Location.EXTERIOR];
		}
	}
}
extend$1(IntersectionMatrix.prototype, {
	isIntersects: function () {
		return !this.isDisjoint();
	},
	isCovers: function () {
		var hasPointInCommon = IntersectionMatrix.isTrue(this.matrix[Location.INTERIOR][Location.INTERIOR]) || IntersectionMatrix.isTrue(this.matrix[Location.INTERIOR][Location.BOUNDARY]) || IntersectionMatrix.isTrue(this.matrix[Location.BOUNDARY][Location.INTERIOR]) || IntersectionMatrix.isTrue(this.matrix[Location.BOUNDARY][Location.BOUNDARY]);
		return hasPointInCommon && this.matrix[Location.EXTERIOR][Location.INTERIOR] === Dimension.FALSE && this.matrix[Location.EXTERIOR][Location.BOUNDARY] === Dimension.FALSE;
	},
	isCoveredBy: function () {
		var hasPointInCommon = IntersectionMatrix.isTrue(this.matrix[Location.INTERIOR][Location.INTERIOR]) || IntersectionMatrix.isTrue(this.matrix[Location.INTERIOR][Location.BOUNDARY]) || IntersectionMatrix.isTrue(this.matrix[Location.BOUNDARY][Location.INTERIOR]) || IntersectionMatrix.isTrue(this.matrix[Location.BOUNDARY][Location.BOUNDARY]);
		return hasPointInCommon && this.matrix[Location.INTERIOR][Location.EXTERIOR] === Dimension.FALSE && this.matrix[Location.BOUNDARY][Location.EXTERIOR] === Dimension.FALSE;
	},
	set: function () {
		if (arguments.length === 1) {
			let dimensionSymbols = arguments[0];
			for (var i = 0; i < dimensionSymbols.length; i++) {
				var row = Math.trunc(i / 3);
				var col = i % 3;
				this.matrix[row][col] = Dimension.toDimensionValue(dimensionSymbols.charAt(i));
			}
		} else if (arguments.length === 3) {
			let row = arguments[0], column = arguments[1], dimensionValue = arguments[2];
			this.matrix[row][column] = dimensionValue;
		}
	},
	isContains: function () {
		return IntersectionMatrix.isTrue(this.matrix[Location.INTERIOR][Location.INTERIOR]) && this.matrix[Location.EXTERIOR][Location.INTERIOR] === Dimension.FALSE && this.matrix[Location.EXTERIOR][Location.BOUNDARY] === Dimension.FALSE;
	},
	setAtLeast: function () {
		if (arguments.length === 1) {
			let minimumDimensionSymbols = arguments[0];
			for (var i = 0; i < minimumDimensionSymbols.length; i++) {
				var row = Math.trunc(i / 3);
				var col = i % 3;
				this.setAtLeast(row, col, Dimension.toDimensionValue(minimumDimensionSymbols.charAt(i)));
			}
		} else if (arguments.length === 3) {
			let row = arguments[0], column = arguments[1], minimumDimensionValue = arguments[2];
			if (this.matrix[row][column] < minimumDimensionValue) {
				this.matrix[row][column] = minimumDimensionValue;
			}
		}
	},
	setAtLeastIfValid: function (row, column, minimumDimensionValue) {
		if (row >= 0 && column >= 0) {
			this.setAtLeast(row, column, minimumDimensionValue);
		}
	},
	isWithin: function () {
		return IntersectionMatrix.isTrue(this.matrix[Location.INTERIOR][Location.INTERIOR]) && this.matrix[Location.INTERIOR][Location.EXTERIOR] === Dimension.FALSE && this.matrix[Location.BOUNDARY][Location.EXTERIOR] === Dimension.FALSE;
	},
	isTouches: function (dimensionOfGeometryA, dimensionOfGeometryB) {
		if (dimensionOfGeometryA > dimensionOfGeometryB) {
			return this.isTouches(dimensionOfGeometryB, dimensionOfGeometryA);
		}
		if (dimensionOfGeometryA === Dimension.A && dimensionOfGeometryB === Dimension.A || dimensionOfGeometryA === Dimension.L && dimensionOfGeometryB === Dimension.L || dimensionOfGeometryA === Dimension.L && dimensionOfGeometryB === Dimension.A || dimensionOfGeometryA === Dimension.P && dimensionOfGeometryB === Dimension.A || dimensionOfGeometryA === Dimension.P && dimensionOfGeometryB === Dimension.L) {
			return this.matrix[Location.INTERIOR][Location.INTERIOR] === Dimension.FALSE && (IntersectionMatrix.isTrue(this.matrix[Location.INTERIOR][Location.BOUNDARY]) || IntersectionMatrix.isTrue(this.matrix[Location.BOUNDARY][Location.INTERIOR]) || IntersectionMatrix.isTrue(this.matrix[Location.BOUNDARY][Location.BOUNDARY]));
		}
		return false;
	},
	isOverlaps: function (dimensionOfGeometryA, dimensionOfGeometryB) {
		if (dimensionOfGeometryA === Dimension.P && dimensionOfGeometryB === Dimension.P || dimensionOfGeometryA === Dimension.A && dimensionOfGeometryB === Dimension.A) {
			return IntersectionMatrix.isTrue(this.matrix[Location.INTERIOR][Location.INTERIOR]) && IntersectionMatrix.isTrue(this.matrix[Location.INTERIOR][Location.EXTERIOR]) && IntersectionMatrix.isTrue(this.matrix[Location.EXTERIOR][Location.INTERIOR]);
		}
		if (dimensionOfGeometryA === Dimension.L && dimensionOfGeometryB === Dimension.L) {
			return this.matrix[Location.INTERIOR][Location.INTERIOR] === 1 && IntersectionMatrix.isTrue(this.matrix[Location.INTERIOR][Location.EXTERIOR]) && IntersectionMatrix.isTrue(this.matrix[Location.EXTERIOR][Location.INTERIOR]);
		}
		return false;
	},
	isEquals: function (dimensionOfGeometryA, dimensionOfGeometryB) {
		if (dimensionOfGeometryA !== dimensionOfGeometryB) {
			return false;
		}
		return IntersectionMatrix.isTrue(this.matrix[Location.INTERIOR][Location.INTERIOR]) && this.matrix[Location.INTERIOR][Location.EXTERIOR] === Dimension.FALSE && this.matrix[Location.BOUNDARY][Location.EXTERIOR] === Dimension.FALSE && this.matrix[Location.EXTERIOR][Location.INTERIOR] === Dimension.FALSE && this.matrix[Location.EXTERIOR][Location.BOUNDARY] === Dimension.FALSE;
	},
	toString: function () {
		var buf = new StringBuffer("123456789");
		for (var ai = 0; ai < 3; ai++) {
			for (var bi = 0; bi < 3; bi++) {
				buf.setCharAt(3 * ai + bi, Dimension.toDimensionSymbol(this.matrix[ai][bi]));
			}
		}
		return buf.toString();
	},
	setAll: function (dimensionValue) {
		for (var ai = 0; ai < 3; ai++) {
			for (var bi = 0; bi < 3; bi++) {
				this.matrix[ai][bi] = dimensionValue;
			}
		}
	},
	get: function (row, column) {
		return this.matrix[row][column];
	},
	transpose: function () {
		var temp = this.matrix[1][0];
		this.matrix[1][0] = this.matrix[0][1];
		this.matrix[0][1] = temp;
		temp = this.matrix[2][0];
		this.matrix[2][0] = this.matrix[0][2];
		this.matrix[0][2] = temp;
		temp = this.matrix[2][1];
		this.matrix[2][1] = this.matrix[1][2];
		this.matrix[1][2] = temp;
		return this;
	},
	matches: function (requiredDimensionSymbols) {
		if (requiredDimensionSymbols.length !== 9) {
			throw new IllegalArgumentException("Should be length 9: " + requiredDimensionSymbols);
		}
		for (var ai = 0; ai < 3; ai++) {
			for (var bi = 0; bi < 3; bi++) {
				if (!IntersectionMatrix.matches(this.matrix[ai][bi], requiredDimensionSymbols.charAt(3 * ai + bi))) {
					return false;
				}
			}
		}
		return true;
	},
	add: function (im) {
		for (var i = 0; i < 3; i++) {
			for (var j = 0; j < 3; j++) {
				this.setAtLeast(i, j, im.get(i, j));
			}
		}
	},
	isDisjoint: function () {
		return this.matrix[Location.INTERIOR][Location.INTERIOR] === Dimension.FALSE && this.matrix[Location.INTERIOR][Location.BOUNDARY] === Dimension.FALSE && this.matrix[Location.BOUNDARY][Location.INTERIOR] === Dimension.FALSE && this.matrix[Location.BOUNDARY][Location.BOUNDARY] === Dimension.FALSE;
	},
	isCrosses: function (dimensionOfGeometryA, dimensionOfGeometryB) {
		if (dimensionOfGeometryA === Dimension.P && dimensionOfGeometryB === Dimension.L || dimensionOfGeometryA === Dimension.P && dimensionOfGeometryB === Dimension.A || dimensionOfGeometryA === Dimension.L && dimensionOfGeometryB === Dimension.A) {
			return IntersectionMatrix.isTrue(this.matrix[Location.INTERIOR][Location.INTERIOR]) && IntersectionMatrix.isTrue(this.matrix[Location.INTERIOR][Location.EXTERIOR]);
		}
		if (dimensionOfGeometryA === Dimension.L && dimensionOfGeometryB === Dimension.P || dimensionOfGeometryA === Dimension.A && dimensionOfGeometryB === Dimension.P || dimensionOfGeometryA === Dimension.A && dimensionOfGeometryB === Dimension.L) {
			return IntersectionMatrix.isTrue(this.matrix[Location.INTERIOR][Location.INTERIOR]) && IntersectionMatrix.isTrue(this.matrix[Location.EXTERIOR][Location.INTERIOR]);
		}
		if (dimensionOfGeometryA === Dimension.L && dimensionOfGeometryB === Dimension.L) {
			return this.matrix[Location.INTERIOR][Location.INTERIOR] === 0;
		}
		return false;
	},
	interfaces_: function () {
		return [Clonable];
	},
	getClass: function () {
		return IntersectionMatrix;
	}
});
IntersectionMatrix.matches = function () {
	if (Number.isInteger(arguments[0]) && typeof arguments[1] === "string") {
		let actualDimensionValue = arguments[0], requiredDimensionSymbol = arguments[1];
		if (requiredDimensionSymbol === Dimension.SYM_DONTCARE) {
			return true;
		}
		if (requiredDimensionSymbol === Dimension.SYM_TRUE && (actualDimensionValue >= 0 || actualDimensionValue === Dimension.TRUE)) {
			return true;
		}
		if (requiredDimensionSymbol === Dimension.SYM_FALSE && actualDimensionValue === Dimension.FALSE) {
			return true;
		}
		if (requiredDimensionSymbol === Dimension.SYM_P && actualDimensionValue === Dimension.P) {
			return true;
		}
		if (requiredDimensionSymbol === Dimension.SYM_L && actualDimensionValue === Dimension.L) {
			return true;
		}
		if (requiredDimensionSymbol === Dimension.SYM_A && actualDimensionValue === Dimension.A) {
			return true;
		}
		return false;
	} else if (typeof arguments[0] === "string" && typeof arguments[1] === "string") {
		let actualDimensionSymbols = arguments[0], requiredDimensionSymbols = arguments[1];
		var m = new IntersectionMatrix(actualDimensionSymbols);
		return m.matches(requiredDimensionSymbols);
	}
};
IntersectionMatrix.isTrue = function (actualDimensionValue) {
	if (actualDimensionValue >= 0 || actualDimensionValue === Dimension.TRUE) {
		return true;
	}
	return false;
};

function EdgeEndBuilder() {}
extend$1(EdgeEndBuilder.prototype, {
	createEdgeEndForNext: function (edge, l, eiCurr, eiNext) {
		var iNext = eiCurr.segmentIndex + 1;
		if (iNext >= edge.getNumPoints() && eiNext === null) return null;
		var pNext = edge.getCoordinate(iNext);
		if (eiNext !== null && eiNext.segmentIndex === eiCurr.segmentIndex) pNext = eiNext.coord;
		var e = new EdgeEnd(edge, eiCurr.coord, pNext, new Label(edge.getLabel()));
		l.add(e);
	},
	createEdgeEndForPrev: function (edge, l, eiCurr, eiPrev) {
		var iPrev = eiCurr.segmentIndex;
		if (eiCurr.dist === 0.0) {
			if (iPrev === 0) return null;
			iPrev--;
		}
		var pPrev = edge.getCoordinate(iPrev);
		if (eiPrev !== null && eiPrev.segmentIndex >= iPrev) pPrev = eiPrev.coord;
		var label = new Label(edge.getLabel());
		label.flip();
		var e = new EdgeEnd(edge, eiCurr.coord, pPrev, label);
		l.add(e);
	},
	computeEdgeEnds: function () {
		if (arguments.length === 1) {
			let edges = arguments[0];
			var l = new ArrayList();
			for (var i = edges; i.hasNext(); ) {
				var e = i.next();
				this.computeEdgeEnds(e, l);
			}
			return l;
		} else if (arguments.length === 2) {
			let edge = arguments[0], l = arguments[1];
			var eiList = edge.getEdgeIntersectionList();
			eiList.addEndpoints();
			var it = eiList.iterator();
			var eiPrev = null;
			var eiCurr = null;
			if (!it.hasNext()) return null;
			var eiNext = it.next();
			do {
				eiPrev = eiCurr;
				eiCurr = eiNext;
				eiNext = null;
				if (it.hasNext()) eiNext = it.next();
				if (eiCurr !== null) {
					this.createEdgeEndForPrev(edge, l, eiCurr, eiPrev);
					this.createEdgeEndForNext(edge, l, eiCurr, eiNext);
				}
			} while (eiCurr !== null);
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return EdgeEndBuilder;
	}
});

function SimplePointInAreaLocator() {
	this.geom = null;
	let geom = arguments[0];
	this.geom = geom;
}
extend$1(SimplePointInAreaLocator.prototype, {
	locate: function (p) {
		return SimplePointInAreaLocator.locate(p, this.geom);
	},
	interfaces_: function () {
		return [PointOnGeometryLocator];
	},
	getClass: function () {
		return SimplePointInAreaLocator;
	}
});
SimplePointInAreaLocator.isPointInRing = function (p, ring) {
	if (!ring.getEnvelopeInternal().intersects(p)) return false;
	return CGAlgorithms.isPointInRing(p, ring.getCoordinates());
};
SimplePointInAreaLocator.containsPointInPolygon = function (p, poly) {
	if (poly.isEmpty()) return false;
	var shell = poly.getExteriorRing();
	if (!SimplePointInAreaLocator.isPointInRing(p, shell)) return false;
	for (var i = 0; i < poly.getNumInteriorRing(); i++) {
		var hole = poly.getInteriorRingN(i);
		if (SimplePointInAreaLocator.isPointInRing(p, hole)) return false;
	}
	return true;
};
SimplePointInAreaLocator.containsPoint = function (p, geom) {
	if (geom instanceof Polygon) {
		return SimplePointInAreaLocator.containsPointInPolygon(p, geom);
	} else if (geom instanceof GeometryCollection) {
		var geomi = new GeometryCollectionIterator(geom);
		while (geomi.hasNext()) {
			var g2 = geomi.next();
			if (g2 !== geom) if (SimplePointInAreaLocator.containsPoint(p, g2)) return true;
		}
	}
	return false;
};
SimplePointInAreaLocator.locate = function (p, geom) {
	if (geom.isEmpty()) return Location.EXTERIOR;
	if (SimplePointInAreaLocator.containsPoint(p, geom)) return Location.INTERIOR;
	return Location.EXTERIOR;
};

function EdgeEndStar() {
	this.edgeMap = new TreeMap();
	this.edgeList = null;
	this.ptInAreaLocation = [Location.NONE, Location.NONE];
}
extend$1(EdgeEndStar.prototype, {
	getNextCW: function (ee) {
		this.getEdges();
		var i = this.edgeList.indexOf(ee);
		var iNextCW = i - 1;
		if (i === 0) iNextCW = this.edgeList.size() - 1;
		return this.edgeList.get(iNextCW);
	},
	propagateSideLabels: function (geomIndex) {
		var startLoc = Location.NONE;
		for (var it = this.iterator(); it.hasNext(); ) {
			var e = it.next();
			var label = e.getLabel();
			if (label.isArea(geomIndex) && label.getLocation(geomIndex, Position.LEFT) !== Location.NONE) startLoc = label.getLocation(geomIndex, Position.LEFT);
		}
		if (startLoc === Location.NONE) return null;
		var currLoc = startLoc;
		for (var it = this.iterator(); it.hasNext(); ) {
			var e = it.next();
			var label = e.getLabel();
			if (label.getLocation(geomIndex, Position.ON) === Location.NONE) label.setLocation(geomIndex, Position.ON, currLoc);
			if (label.isArea(geomIndex)) {
				var leftLoc = label.getLocation(geomIndex, Position.LEFT);
				var rightLoc = label.getLocation(geomIndex, Position.RIGHT);
				if (rightLoc !== Location.NONE) {
					if (rightLoc !== currLoc) throw new TopologyException("side location conflict", e.getCoordinate());
					if (leftLoc === Location.NONE) {
						Assert.shouldNeverReachHere("found single null side (at " + e.getCoordinate() + ")");
					}
					currLoc = leftLoc;
				} else {
					Assert.isTrue(label.getLocation(geomIndex, Position.LEFT) === Location.NONE, "found single null side");
					label.setLocation(geomIndex, Position.RIGHT, currLoc);
					label.setLocation(geomIndex, Position.LEFT, currLoc);
				}
			}
		}
	},
	getCoordinate: function () {
		var it = this.iterator();
		if (!it.hasNext()) return null;
		var e = it.next();
		return e.getCoordinate();
	},
	print: function (out) {
		System.out.println("EdgeEndStar:   " + this.getCoordinate());
		for (var it = this.iterator(); it.hasNext(); ) {
			var e = it.next();
			e.print(out);
		}
	},
	isAreaLabelsConsistent: function (geomGraph) {
		this.computeEdgeEndLabels(geomGraph.getBoundaryNodeRule());
		return this.checkAreaLabelsConsistent(0);
	},
	checkAreaLabelsConsistent: function (geomIndex) {
		var edges = this.getEdges();
		if (edges.size() <= 0) return true;
		var lastEdgeIndex = edges.size() - 1;
		var startLabel = edges.get(lastEdgeIndex).getLabel();
		var startLoc = startLabel.getLocation(geomIndex, Position.LEFT);
		Assert.isTrue(startLoc !== Location.NONE, "Found unlabelled area edge");
		var currLoc = startLoc;
		for (var it = this.iterator(); it.hasNext(); ) {
			var e = it.next();
			var label = e.getLabel();
			Assert.isTrue(label.isArea(geomIndex), "Found non-area edge");
			var leftLoc = label.getLocation(geomIndex, Position.LEFT);
			var rightLoc = label.getLocation(geomIndex, Position.RIGHT);
			if (leftLoc === rightLoc) {
				return false;
			}
			if (rightLoc !== currLoc) {
				return false;
			}
			currLoc = leftLoc;
		}
		return true;
	},
	findIndex: function (eSearch) {
		this.iterator();
		for (var i = 0; i < this.edgeList.size(); i++) {
			var e = this.edgeList.get(i);
			if (e === eSearch) return i;
		}
		return -1;
	},
	iterator: function () {
		return this.getEdges().iterator();
	},
	getEdges: function () {
		if (this.edgeList === null) {
			this.edgeList = new ArrayList(this.edgeMap.values());
		}
		return this.edgeList;
	},
	getLocation: function (geomIndex, p, geom) {
		if (this.ptInAreaLocation[geomIndex] === Location.NONE) {
			this.ptInAreaLocation[geomIndex] = SimplePointInAreaLocator.locate(p, geom[geomIndex].getGeometry());
		}
		return this.ptInAreaLocation[geomIndex];
	},
	toString: function () {
		var buf = new StringBuffer();
		buf.append("EdgeEndStar:   " + this.getCoordinate());
		buf.append("\n");
		for (var it = this.iterator(); it.hasNext(); ) {
			var e = it.next();
			buf.append(e);
			buf.append("\n");
		}
		return buf.toString();
	},
	computeEdgeEndLabels: function (boundaryNodeRule) {
		for (var it = this.iterator(); it.hasNext(); ) {
			var ee = it.next();
			ee.computeLabel(boundaryNodeRule);
		}
	},
	computeLabelling: function (geomGraph) {
		this.computeEdgeEndLabels(geomGraph[0].getBoundaryNodeRule());
		this.propagateSideLabels(0);
		this.propagateSideLabels(1);
		var hasDimensionalCollapseEdge = [false, false];
		for (var it = this.iterator(); it.hasNext(); ) {
			var e = it.next();
			var label = e.getLabel();
			for (var geomi = 0; geomi < 2; geomi++) {
				if (label.isLine(geomi) && label.getLocation(geomi) === Location.BOUNDARY) hasDimensionalCollapseEdge[geomi] = true;
			}
		}
		for (var it = this.iterator(); it.hasNext(); ) {
			var e = it.next();
			var label = e.getLabel();
			for (var geomi = 0; geomi < 2; geomi++) {
				if (label.isAnyNull(geomi)) {
					var loc = Location.NONE;
					if (hasDimensionalCollapseEdge[geomi]) {
						loc = Location.EXTERIOR;
					} else {
						var p = e.getCoordinate();
						loc = this.getLocation(geomi, p, geomGraph);
					}
					label.setAllLocationsIfNull(geomi, loc);
				}
			}
		}
	},
	getDegree: function () {
		return this.edgeMap.size();
	},
	insertEdgeEnd: function (e, obj) {
		this.edgeMap.put(e, obj);
		this.edgeList = null;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return EdgeEndStar;
	}
});

function EdgeEndBundle() {
	this.edgeEnds = new ArrayList();
	if (arguments.length === 1) {
		let e = arguments[0];
		EdgeEndBundle.call(this, null, e);
	} else if (arguments.length === 2) {
		let boundaryNodeRule = arguments[0], e = arguments[1];
		EdgeEnd.call(this, e.getEdge(), e.getCoordinate(), e.getDirectedCoordinate(), new Label(e.getLabel()));
		this.insert(e);
	}
}
inherits(EdgeEndBundle, EdgeEnd);
extend$1(EdgeEndBundle.prototype, {
	insert: function (e) {
		this.edgeEnds.add(e);
	},
	print: function (out) {
		out.println("EdgeEndBundle--> Label: " + this.label);
		for (var it = this.iterator(); it.hasNext(); ) {
			var ee = it.next();
			ee.print(out);
			out.println();
		}
	},
	iterator: function () {
		return this.edgeEnds.iterator();
	},
	getEdgeEnds: function () {
		return this.edgeEnds;
	},
	computeLabelOn: function (geomIndex, boundaryNodeRule) {
		var boundaryCount = 0;
		var foundInterior = false;
		for (var it = this.iterator(); it.hasNext(); ) {
			var e = it.next();
			var loc = e.getLabel().getLocation(geomIndex);
			if (loc === Location.BOUNDARY) boundaryCount++;
			if (loc === Location.INTERIOR) foundInterior = true;
		}
		var loc = Location.NONE;
		if (foundInterior) loc = Location.INTERIOR;
		if (boundaryCount > 0) {
			loc = GeometryGraph.determineBoundary(boundaryNodeRule, boundaryCount);
		}
		this.label.setLocation(geomIndex, loc);
	},
	computeLabelSide: function (geomIndex, side) {
		for (var it = this.iterator(); it.hasNext(); ) {
			var e = it.next();
			if (e.getLabel().isArea()) {
				var loc = e.getLabel().getLocation(geomIndex, side);
				if (loc === Location.INTERIOR) {
					this.label.setLocation(geomIndex, side, Location.INTERIOR);
					return null;
				} else if (loc === Location.EXTERIOR) this.label.setLocation(geomIndex, side, Location.EXTERIOR);
			}
		}
	},
	getLabel: function () {
		return this.label;
	},
	computeLabelSides: function (geomIndex) {
		this.computeLabelSide(geomIndex, Position.LEFT);
		this.computeLabelSide(geomIndex, Position.RIGHT);
	},
	updateIM: function (im) {
		Edge.updateIM(this.label, im);
	},
	computeLabel: function (boundaryNodeRule) {
		var isArea = false;
		for (var it = this.iterator(); it.hasNext(); ) {
			var e = it.next();
			if (e.getLabel().isArea()) isArea = true;
		}
		if (isArea) this.label = new Label(Location.NONE, Location.NONE, Location.NONE); else this.label = new Label(Location.NONE);
		for (var i = 0; i < 2; i++) {
			this.computeLabelOn(i, boundaryNodeRule);
			if (isArea) this.computeLabelSides(i);
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return EdgeEndBundle;
	}
});

function EdgeEndBundleStar() {
	EdgeEndStar.apply(this);
}
inherits(EdgeEndBundleStar, EdgeEndStar);
extend$1(EdgeEndBundleStar.prototype, {
	updateIM: function (im) {
		for (var it = this.iterator(); it.hasNext(); ) {
			var esb = it.next();
			esb.updateIM(im);
		}
	},
	insert: function (e) {
		var eb = this.edgeMap.get(e);
		if (eb === null) {
			eb = new EdgeEndBundle(e);
			this.insertEdgeEnd(e, eb);
		} else {
			eb.insert(e);
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return EdgeEndBundleStar;
	}
});

function RelateNode() {
	let coord = arguments[0], edges = arguments[1];
	Node.call(this, coord, edges);
}
inherits(RelateNode, Node);
extend$1(RelateNode.prototype, {
	updateIMFromEdges: function (im) {
		this.edges.updateIM(im);
	},
	computeIM: function (im) {
		im.setAtLeastIfValid(this.label.getLocation(0), this.label.getLocation(1), 0);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return RelateNode;
	}
});

function RelateNodeFactory() {
	NodeFactory.apply(this);
}
inherits(RelateNodeFactory, NodeFactory);
extend$1(RelateNodeFactory.prototype, {
	createNode: function (coord) {
		return new RelateNode(coord, new EdgeEndBundleStar());
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return RelateNodeFactory;
	}
});

function RelateComputer() {
	this.li = new RobustLineIntersector();
	this.ptLocator = new PointLocator();
	this.arg = null;
	this.nodes = new NodeMap(new RelateNodeFactory());
	this.im = null;
	this.isolatedEdges = new ArrayList();
	this.invalidPoint = null;
	let arg = arguments[0];
	this.arg = arg;
}
extend$1(RelateComputer.prototype, {
	insertEdgeEnds: function (ee) {
		for (var i = ee.iterator(); i.hasNext(); ) {
			var e = i.next();
			this.nodes.add(e);
		}
	},
	computeProperIntersectionIM: function (intersector, im) {
		var dimA = this.arg[0].getGeometry().getDimension();
		var dimB = this.arg[1].getGeometry().getDimension();
		var hasProper = intersector.hasProperIntersection();
		var hasProperInterior = intersector.hasProperInteriorIntersection();
		if (dimA === 2 && dimB === 2) {
			if (hasProper) im.setAtLeast("212101212");
		} else if (dimA === 2 && dimB === 1) {
			if (hasProper) im.setAtLeast("FFF0FFFF2");
			if (hasProperInterior) im.setAtLeast("1FFFFF1FF");
		} else if (dimA === 1 && dimB === 2) {
			if (hasProper) im.setAtLeast("F0FFFFFF2");
			if (hasProperInterior) im.setAtLeast("1F1FFFFFF");
		} else if (dimA === 1 && dimB === 1) {
			if (hasProperInterior) im.setAtLeast("0FFFFFFFF");
		}
	},
	labelIsolatedEdges: function (thisIndex, targetIndex) {
		for (var ei = this.arg[thisIndex].getEdgeIterator(); ei.hasNext(); ) {
			var e = ei.next();
			if (e.isIsolated()) {
				this.labelIsolatedEdge(e, targetIndex, this.arg[targetIndex].getGeometry());
				this.isolatedEdges.add(e);
			}
		}
	},
	labelIsolatedEdge: function (e, targetIndex, target) {
		if (target.getDimension() > 0) {
			var loc = this.ptLocator.locate(e.getCoordinate(), target);
			e.getLabel().setAllLocations(targetIndex, loc);
		} else {
			e.getLabel().setAllLocations(targetIndex, Location.EXTERIOR);
		}
	},
	computeIM: function () {
		var im = new IntersectionMatrix();
		im.set(Location.EXTERIOR, Location.EXTERIOR, 2);
		if (!this.arg[0].getGeometry().getEnvelopeInternal().intersects(this.arg[1].getGeometry().getEnvelopeInternal())) {
			this.computeDisjointIM(im);
			return im;
		}
		this.arg[0].computeSelfNodes(this.li, false);
		this.arg[1].computeSelfNodes(this.li, false);
		var intersector = this.arg[0].computeEdgeIntersections(this.arg[1], this.li, false);
		this.computeIntersectionNodes(0);
		this.computeIntersectionNodes(1);
		this.copyNodesAndLabels(0);
		this.copyNodesAndLabels(1);
		this.labelIsolatedNodes();
		this.computeProperIntersectionIM(intersector, im);
		var eeBuilder = new EdgeEndBuilder();
		var ee0 = eeBuilder.computeEdgeEnds(this.arg[0].getEdgeIterator());
		this.insertEdgeEnds(ee0);
		var ee1 = eeBuilder.computeEdgeEnds(this.arg[1].getEdgeIterator());
		this.insertEdgeEnds(ee1);
		this.labelNodeEdges();
		this.labelIsolatedEdges(0, 1);
		this.labelIsolatedEdges(1, 0);
		this.updateIM(im);
		return im;
	},
	labelNodeEdges: function () {
		for (var ni = this.nodes.iterator(); ni.hasNext(); ) {
			var node = ni.next();
			node.getEdges().computeLabelling(this.arg);
		}
	},
	copyNodesAndLabels: function (argIndex) {
		for (var i = this.arg[argIndex].getNodeIterator(); i.hasNext(); ) {
			var graphNode = i.next();
			var newNode = this.nodes.addNode(graphNode.getCoordinate());
			newNode.setLabel(argIndex, graphNode.getLabel().getLocation(argIndex));
		}
	},
	labelIntersectionNodes: function (argIndex) {
		for (var i = this.arg[argIndex].getEdgeIterator(); i.hasNext(); ) {
			var e = i.next();
			var eLoc = e.getLabel().getLocation(argIndex);
			for (var eiIt = e.getEdgeIntersectionList().iterator(); eiIt.hasNext(); ) {
				var ei = eiIt.next();
				var n = this.nodes.find(ei.coord);
				if (n.getLabel().isNull(argIndex)) {
					if (eLoc === Location.BOUNDARY) n.setLabelBoundary(argIndex); else n.setLabel(argIndex, Location.INTERIOR);
				}
			}
		}
	},
	labelIsolatedNode: function (n, targetIndex) {
		var loc = this.ptLocator.locate(n.getCoordinate(), this.arg[targetIndex].getGeometry());
		n.getLabel().setAllLocations(targetIndex, loc);
	},
	computeIntersectionNodes: function (argIndex) {
		for (var i = this.arg[argIndex].getEdgeIterator(); i.hasNext(); ) {
			var e = i.next();
			var eLoc = e.getLabel().getLocation(argIndex);
			for (var eiIt = e.getEdgeIntersectionList().iterator(); eiIt.hasNext(); ) {
				var ei = eiIt.next();
				var n = this.nodes.addNode(ei.coord);
				if (eLoc === Location.BOUNDARY) n.setLabelBoundary(argIndex); else {
					if (n.getLabel().isNull(argIndex)) n.setLabel(argIndex, Location.INTERIOR);
				}
			}
		}
	},
	labelIsolatedNodes: function () {
		for (var ni = this.nodes.iterator(); ni.hasNext(); ) {
			var n = ni.next();
			var label = n.getLabel();
			Assert.isTrue(label.getGeometryCount() > 0, "node with empty label found");
			if (n.isIsolated()) {
				if (label.isNull(0)) this.labelIsolatedNode(n, 0); else this.labelIsolatedNode(n, 1);
			}
		}
	},
	updateIM: function (im) {
		for (var ei = this.isolatedEdges.iterator(); ei.hasNext(); ) {
			var e = ei.next();
			e.updateIM(im);
		}
		for (var ni = this.nodes.iterator(); ni.hasNext(); ) {
			var node = ni.next();
			node.updateIM(im);
			node.updateIMFromEdges(im);
		}
	},
	computeDisjointIM: function (im) {
		var ga = this.arg[0].getGeometry();
		if (!ga.isEmpty()) {
			im.set(Location.INTERIOR, Location.EXTERIOR, ga.getDimension());
			im.set(Location.BOUNDARY, Location.EXTERIOR, ga.getBoundaryDimension());
		}
		var gb = this.arg[1].getGeometry();
		if (!gb.isEmpty()) {
			im.set(Location.EXTERIOR, Location.INTERIOR, gb.getDimension());
			im.set(Location.EXTERIOR, Location.BOUNDARY, gb.getBoundaryDimension());
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return RelateComputer;
	}
});

function GeometryGraphOperation() {
	this.li = new RobustLineIntersector();
	this.resultPrecisionModel = null;
	this.arg = null;
	if (arguments.length === 1) {
		let g0 = arguments[0];
		this.setComputationPrecision(g0.getPrecisionModel());
		this.arg = new Array(1).fill(null);
		this.arg[0] = new GeometryGraph(0, g0);

	} else if (arguments.length === 2) {
		let g0 = arguments[0], g1 = arguments[1];
		GeometryGraphOperation.call(this, g0, g1, BoundaryNodeRule.OGC_SFS_BOUNDARY_RULE);
	} else if (arguments.length === 3) {
		let g0 = arguments[0], g1 = arguments[1], boundaryNodeRule = arguments[2];
		if (g0.getPrecisionModel().compareTo(g1.getPrecisionModel()) >= 0) this.setComputationPrecision(g0.getPrecisionModel()); else this.setComputationPrecision(g1.getPrecisionModel());
		this.arg = new Array(2).fill(null);
		this.arg[0] = new GeometryGraph(0, g0, boundaryNodeRule);
		this.arg[1] = new GeometryGraph(1, g1, boundaryNodeRule);
	}
}
extend$1(GeometryGraphOperation.prototype, {
	getArgGeometry: function (i) {
		return this.arg[i].getGeometry();
	},
	setComputationPrecision: function (pm) {
		this.resultPrecisionModel = pm;
		this.li.setPrecisionModel(this.resultPrecisionModel);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return GeometryGraphOperation;
	}
});

function RectangleContains() {
	this.rectEnv = null;
	let rectangle = arguments[0];
	this.rectEnv = rectangle.getEnvelopeInternal();
}
extend$1(RectangleContains.prototype, {
	isContainedInBoundary: function (geom) {
		if (geom instanceof Polygon) return false;
		if (geom instanceof Point) return this.isPointContainedInBoundary(geom);
		if (geom instanceof LineString) return this.isLineStringContainedInBoundary(geom);
		for (var i = 0; i < geom.getNumGeometries(); i++) {
			var comp = geom.getGeometryN(i);
			if (!this.isContainedInBoundary(comp)) return false;
		}
		return true;
	},
	isLineSegmentContainedInBoundary: function (p0, p1) {
		if (p0.equals(p1)) return this.isPointContainedInBoundary(p0);
		if (p0.x === p1.x) {
			if (p0.x === this.rectEnv.getMinX() || p0.x === this.rectEnv.getMaxX()) return true;
		} else if (p0.y === p1.y) {
			if (p0.y === this.rectEnv.getMinY() || p0.y === this.rectEnv.getMaxY()) return true;
		}
		return false;
	},
	isLineStringContainedInBoundary: function (line) {
		var seq = line.getCoordinateSequence();
		var p0 = new Coordinate();
		var p1 = new Coordinate();
		for (var i = 0; i < seq.size() - 1; i++) {
			seq.getCoordinate(i, p0);
			seq.getCoordinate(i + 1, p1);
			if (!this.isLineSegmentContainedInBoundary(p0, p1)) return false;
		}
		return true;
	},
	isPointContainedInBoundary: function () {
		if (arguments[0] instanceof Point) {
			let point = arguments[0];
			return this.isPointContainedInBoundary(point.getCoordinate());
		} else if (arguments[0] instanceof Coordinate) {
			let pt = arguments[0];
			return pt.x === this.rectEnv.getMinX() || pt.x === this.rectEnv.getMaxX() || pt.y === this.rectEnv.getMinY() || pt.y === this.rectEnv.getMaxY();
		}
	},
	contains: function (geom) {
		if (!this.rectEnv.contains(geom.getEnvelopeInternal())) return false;
		if (this.isContainedInBoundary(geom)) return false;
		return true;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return RectangleContains;
	}
});
RectangleContains.contains = function (rectangle, b) {
	var rc = new RectangleContains(rectangle);
	return rc.contains(b);
};

function RectangleLineIntersector() {
	this.li = new RobustLineIntersector();
	this.rectEnv = null;
	this.diagUp0 = null;
	this.diagUp1 = null;
	this.diagDown0 = null;
	this.diagDown1 = null;
	let rectEnv = arguments[0];
	this.rectEnv = rectEnv;
	this.diagUp0 = new Coordinate(rectEnv.getMinX(), rectEnv.getMinY());
	this.diagUp1 = new Coordinate(rectEnv.getMaxX(), rectEnv.getMaxY());
	this.diagDown0 = new Coordinate(rectEnv.getMinX(), rectEnv.getMaxY());
	this.diagDown1 = new Coordinate(rectEnv.getMaxX(), rectEnv.getMinY());
}
extend$1(RectangleLineIntersector.prototype, {
	intersects: function (p0, p1) {
		var segEnv = new Envelope(p0, p1);
		if (!this.rectEnv.intersects(segEnv)) return false;
		if (this.rectEnv.intersects(p0)) return true;
		if (this.rectEnv.intersects(p1)) return true;
		if (p0.compareTo(p1) > 0) {
			var tmp = p0;
			p0 = p1;
			p1 = tmp;
		}
		var isSegUpwards = false;
		if (p1.y > p0.y) isSegUpwards = true;
		if (isSegUpwards) {
			this.li.computeIntersection(p0, p1, this.diagDown0, this.diagDown1);
		} else {
			this.li.computeIntersection(p0, p1, this.diagUp0, this.diagUp1);
		}
		if (this.li.hasIntersection()) return true;
		return false;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return RectangleLineIntersector;
	}
});

function ShortCircuitedGeometryVisitor() {
	this._isDone = false;
}
extend$1(ShortCircuitedGeometryVisitor.prototype, {
	applyTo: function (geom) {
		for (var i = 0; i < geom.getNumGeometries() && !this._isDone; i++) {
			var element = geom.getGeometryN(i);
			if (!(element instanceof GeometryCollection)) {
				this.visit(element);
				if (this.isDone()) {
					this._isDone = true;
					return null;
				}
			} else this.applyTo(element);
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return ShortCircuitedGeometryVisitor;
	}
});

function RectangleIntersects() {
	this.rectangle = null;
	this.rectEnv = null;
	let rectangle = arguments[0];
	this.rectangle = rectangle;
	this.rectEnv = rectangle.getEnvelopeInternal();
}
extend$1(RectangleIntersects.prototype, {
	intersects: function (geom) {
		if (!this.rectEnv.intersects(geom.getEnvelopeInternal())) return false;
		var visitor = new EnvelopeIntersectsVisitor(this.rectEnv);
		visitor.applyTo(geom);
		if (visitor.intersects()) return true;
		var ecpVisitor = new GeometryContainsPointVisitor(this.rectangle);
		ecpVisitor.applyTo(geom);
		if (ecpVisitor.containsPoint()) return true;
		var riVisitor = new RectangleIntersectsSegmentVisitor(this.rectangle);
		riVisitor.applyTo(geom);
		if (riVisitor.intersects()) return true;
		return false;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return RectangleIntersects;
	}
});
RectangleIntersects.intersects = function (rectangle, b) {
	var rp = new RectangleIntersects(rectangle);
	return rp.intersects(b);
};
function EnvelopeIntersectsVisitor() {
	ShortCircuitedGeometryVisitor.apply(this);
	this.rectEnv = null;
	this._intersects = false;
	let rectEnv = arguments[0];
	this.rectEnv = rectEnv;
}
inherits(EnvelopeIntersectsVisitor, ShortCircuitedGeometryVisitor);
extend$1(EnvelopeIntersectsVisitor.prototype, {
	isDone: function () {
		return this._intersects === true;
	},
	visit: function (element) {
		var elementEnv = element.getEnvelopeInternal();
		if (!this.rectEnv.intersects(elementEnv)) {
			return null;
		}
		if (this.rectEnv.contains(elementEnv)) {
			this._intersects = true;
			return null;
		}
		if (elementEnv.getMinX() >= this.rectEnv.getMinX() && elementEnv.getMaxX() <= this.rectEnv.getMaxX()) {
			this._intersects = true;
			return null;
		}
		if (elementEnv.getMinY() >= this.rectEnv.getMinY() && elementEnv.getMaxY() <= this.rectEnv.getMaxY()) {
			this._intersects = true;
			return null;
		}
	},
	intersects: function () {
		return this._intersects;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return EnvelopeIntersectsVisitor;
	}
});
function GeometryContainsPointVisitor() {
	ShortCircuitedGeometryVisitor.apply(this);
	this.rectSeq = null;
	this.rectEnv = null;
	this._containsPoint = false;
	let rectangle = arguments[0];
	this.rectSeq = rectangle.getExteriorRing().getCoordinateSequence();
	this.rectEnv = rectangle.getEnvelopeInternal();
}
inherits(GeometryContainsPointVisitor, ShortCircuitedGeometryVisitor);
extend$1(GeometryContainsPointVisitor.prototype, {
	isDone: function () {
		return this._containsPoint === true;
	},
	visit: function (geom) {
		if (!(geom instanceof Polygon)) return null;
		var elementEnv = geom.getEnvelopeInternal();
		if (!this.rectEnv.intersects(elementEnv)) return null;
		var rectPt = new Coordinate();
		for (var i = 0; i < 4; i++) {
			this.rectSeq.getCoordinate(i, rectPt);
			if (!elementEnv.contains(rectPt)) continue;
			if (SimplePointInAreaLocator.containsPointInPolygon(rectPt, geom)) {
				this._containsPoint = true;
				return null;
			}
		}
	},
	containsPoint: function () {
		return this._containsPoint;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return GeometryContainsPointVisitor;
	}
});
function RectangleIntersectsSegmentVisitor() {
	ShortCircuitedGeometryVisitor.apply(this);
	this.rectEnv = null;
	this.rectIntersector = null;
	this.hasIntersection = false;
	this.p0 = new Coordinate();
	this.p1 = new Coordinate();
	let rectangle = arguments[0];
	this.rectEnv = rectangle.getEnvelopeInternal();
	this.rectIntersector = new RectangleLineIntersector(this.rectEnv);
}
inherits(RectangleIntersectsSegmentVisitor, ShortCircuitedGeometryVisitor);
extend$1(RectangleIntersectsSegmentVisitor.prototype, {
	intersects: function () {
		return this.hasIntersection;
	},
	isDone: function () {
		return this.hasIntersection === true;
	},
	visit: function (geom) {
		var elementEnv = geom.getEnvelopeInternal();
		if (!this.rectEnv.intersects(elementEnv)) return null;
		var lines = LinearComponentExtracter.getLines(geom);
		this.checkIntersectionWithLineStrings(lines);
	},
	checkIntersectionWithLineStrings: function (lines) {
		for (var i = lines.iterator(); i.hasNext(); ) {
			var testLine = i.next();
			this.checkIntersectionWithSegments(testLine);
			if (this.hasIntersection) return null;
		}
	},
	checkIntersectionWithSegments: function (testLine) {
		var seq1 = testLine.getCoordinateSequence();
		for (var j = 1; j < seq1.size(); j++) {
			seq1.getCoordinate(j - 1, this.p0);
			seq1.getCoordinate(j, this.p1);
			if (this.rectIntersector.intersects(this.p0, this.p1)) {
				this.hasIntersection = true;
				return null;
			}
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return RectangleIntersectsSegmentVisitor;
	}
});

function RelateOp() {
	this._relate = null;
	if (arguments.length === 2) {
		let g0 = arguments[0], g1 = arguments[1];
		GeometryGraphOperation.call(this, g0, g1);
		this._relate = new RelateComputer(this.arg);
	} else if (arguments.length === 3) {
		let g0 = arguments[0], g1 = arguments[1], boundaryNodeRule = arguments[2];
		GeometryGraphOperation.call(this, g0, g1, boundaryNodeRule);
		this._relate = new RelateComputer(this.arg);
	}
}
inherits(RelateOp, GeometryGraphOperation);
extend$1(RelateOp.prototype, {
	getIntersectionMatrix: function () {
		return this._relate.computeIM();
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return RelateOp;
	}
});
RelateOp.covers = function (g1, g2) {
	if (!g1.getEnvelopeInternal().covers(g2.getEnvelopeInternal())) return false;
	if (g1.isRectangle()) {
		return true;
	}
	return RelateOp.relate(g1, g2).isCovers();
};
RelateOp.intersects = function (g1, g2) {
	if (!g1.getEnvelopeInternal().intersects(g2.getEnvelopeInternal())) return false;
	if (g1.isRectangle()) {
		return RectangleIntersects.intersects(g1, g2);
	}
	if (g2.isRectangle()) {
		return RectangleIntersects.intersects(g2, g1);
	}
	return RelateOp.relate(g1, g2).isIntersects();
};
RelateOp.touches = function (g1, g2) {
	if (!g1.getEnvelopeInternal().intersects(g2.getEnvelopeInternal())) return false;
	return RelateOp.relate(g1, g2).isTouches(g1.getDimension(), g2.getDimension());
};
RelateOp.within = function (g1, g2) {
	return g2.contains(g1);
};
RelateOp.coveredBy = function (g1, g2) {
	return RelateOp.covers(g2, g1);
};
RelateOp.relate = function () {
	if (arguments.length === 2) {
		let a = arguments[0], b = arguments[1];
		var relOp = new RelateOp(a, b);
		var im = relOp.getIntersectionMatrix();
		return im;
	} else if (arguments.length === 3) {
		if (typeof arguments[2] === "string" && (arguments[0] instanceof Geometry && arguments[1] instanceof Geometry)) {
			let g1 = arguments[0], g2 = arguments[1], intersectionPattern = arguments[2];
			return RelateOp.relateWithCheck(g1, g2).matches(intersectionPattern);
		} else if (hasInterface(arguments[2], BoundaryNodeRule) && (arguments[0] instanceof Geometry && arguments[1] instanceof Geometry)) {
			let a = arguments[0], b = arguments[1], boundaryNodeRule = arguments[2];
			var relOp = new RelateOp(a, b, boundaryNodeRule);
			var im = relOp.getIntersectionMatrix();
			return im;
		}
	}
};
RelateOp.overlaps = function (g1, g2) {
	if (!g1.getEnvelopeInternal().intersects(g2.getEnvelopeInternal())) return false;
	return RelateOp.relate(g1, g2).isOverlaps(g1.getDimension(), g2.getDimension());
};
RelateOp.disjoint = function (g1, g2) {
	return !g1.intersects(g2);
};
RelateOp.relateWithCheck = function (g1, g2) {
	g1.checkNotGeometryCollection(g1);
	g1.checkNotGeometryCollection(g2);
	return RelateOp.relate(g1, g2);
};
RelateOp.crosses = function (g1, g2) {
	if (!g1.getEnvelopeInternal().intersects(g2.getEnvelopeInternal())) return false;
	return RelateOp.relate(g1, g2).isCrosses(g1.getDimension(), g2.getDimension());
};
RelateOp.contains = function (g1, g2) {
	if (!g1.getEnvelopeInternal().contains(g2.getEnvelopeInternal())) return false;
	if (g1.isRectangle()) {
		return RectangleContains.contains(g1, g2);
	}
	return RelateOp.relate(g1, g2).isContains();
};

function PolygonExtracter() {
	this.comps = null;
	let comps = arguments[0];
	this.comps = comps;
}
extend$1(PolygonExtracter.prototype, {
	filter: function (geom) {
		if (geom instanceof Polygon) this.comps.add(geom);
	},
	interfaces_: function () {
		return [GeometryFilter];
	},
	getClass: function () {
		return PolygonExtracter;
	}
});
PolygonExtracter.getPolygons = function () {
	if (arguments.length === 1) {
		let geom = arguments[0];
		return PolygonExtracter.getPolygons(geom, new ArrayList());
	} else if (arguments.length === 2) {
		let geom = arguments[0], list = arguments[1];
		if (geom instanceof Polygon) {
			list.add(geom);
		} else if (geom instanceof GeometryCollection) {
			geom.apply(new PolygonExtracter(list));
		}
		return list;
	}
};

function GeometryLocation() {
	this.component = null;
	this.segIndex = null;
	this.pt = null;
	if (arguments.length === 2) {
		let component = arguments[0], pt = arguments[1];
		GeometryLocation.call(this, component, GeometryLocation.INSIDE_AREA, pt);
	} else if (arguments.length === 3) {
		let component = arguments[0], segIndex = arguments[1], pt = arguments[2];
		this.component = component;
		this.segIndex = segIndex;
		this.pt = pt;
	}
}
extend$1(GeometryLocation.prototype, {
	isInsideArea: function () {
		return this.segIndex === GeometryLocation.INSIDE_AREA;
	},
	getCoordinate: function () {
		return this.pt;
	},
	getGeometryComponent: function () {
		return this.component;
	},
	getSegmentIndex: function () {
		return this.segIndex;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return GeometryLocation;
	}
});
GeometryLocation.INSIDE_AREA = -1;

function PointExtracter() {
	this.pts = null;
	let pts = arguments[0];
	this.pts = pts;
}
extend$1(PointExtracter.prototype, {
	filter: function (geom) {
		if (geom instanceof Point) this.pts.add(geom);
	},
	interfaces_: function () {
		return [GeometryFilter];
	},
	getClass: function () {
		return PointExtracter;
	}
});
PointExtracter.getPoints = function () {
	if (arguments.length === 1) {
		let geom = arguments[0];
		if (geom instanceof Point) {
			return Collections.singletonList(geom);
		}
		return PointExtracter.getPoints(geom, new ArrayList());
	} else if (arguments.length === 2) {
		let geom = arguments[0], list = arguments[1];
		if (geom instanceof Point) {
			list.add(geom);
		} else if (geom instanceof GeometryCollection) {
			geom.apply(new PointExtracter(list));
		}
		return list;
	}
};

function ConnectedElementLocationFilter() {
	this.locations = null;
	let locations = arguments[0];
	this.locations = locations;
}
extend$1(ConnectedElementLocationFilter.prototype, {
	filter: function (geom) {
		if (geom instanceof Point || geom instanceof LineString || geom instanceof Polygon) this.locations.add(new GeometryLocation(geom, 0, geom.getCoordinate()));
	},
	interfaces_: function () {
		return [GeometryFilter];
	},
	getClass: function () {
		return ConnectedElementLocationFilter;
	}
});
ConnectedElementLocationFilter.getLocations = function (geom) {
	var locations = new ArrayList();
	geom.apply(new ConnectedElementLocationFilter(locations));
	return locations;
};

function DistanceOp() {
	this.geom = null;
	this.terminateDistance = 0.0;
	this.ptLocator = new PointLocator();
	this.minDistanceLocation = null;
	this.minDistance = Double.MAX_VALUE;
	if (arguments.length === 2) {
		let g0 = arguments[0], g1 = arguments[1];
		DistanceOp.call(this, g0, g1, 0.0);
	} else if (arguments.length === 3) {
		let g0 = arguments[0], g1 = arguments[1], terminateDistance = arguments[2];
		this.geom = new Array(2).fill(null);
		this.geom[0] = g0;
		this.geom[1] = g1;
		this.terminateDistance = terminateDistance;
	}
}
extend$1(DistanceOp.prototype, {
	computeContainmentDistance: function () {
		if (arguments.length === 0) {
			var locPtPoly = new Array(2).fill(null);
			this.computeContainmentDistance(0, locPtPoly);
			if (this.minDistance <= this.terminateDistance) return null;
			this.computeContainmentDistance(1, locPtPoly);
		} else if (arguments.length === 2) {
			let polyGeomIndex = arguments[0], locPtPoly = arguments[1];
			var locationsIndex = 1 - polyGeomIndex;
			var polys = PolygonExtracter.getPolygons(this.geom[polyGeomIndex]);
			if (polys.size() > 0) {
				var insideLocs = ConnectedElementLocationFilter.getLocations(this.geom[locationsIndex]);
				this.computeContainmentDistance(insideLocs, polys, locPtPoly);
				if (this.minDistance <= this.terminateDistance) {
					this.minDistanceLocation[locationsIndex] = locPtPoly[0];
					this.minDistanceLocation[polyGeomIndex] = locPtPoly[1];
					return null;
				}
			}
		} else if (arguments.length === 3) {
			if (arguments[2] instanceof Array && (hasInterface(arguments[0], List) && hasInterface(arguments[1], List))) {
				let locs = arguments[0], polys = arguments[1], locPtPoly = arguments[2];
				for (var i = 0; i < locs.size(); i++) {
					var loc = locs.get(i);
					for (var j = 0; j < polys.size(); j++) {
						this.computeContainmentDistance(loc, polys.get(j), locPtPoly);
						if (this.minDistance <= this.terminateDistance) return null;
					}
				}
			} else if (arguments[2] instanceof Array && (arguments[0] instanceof GeometryLocation && arguments[1] instanceof Polygon)) {
				let ptLoc = arguments[0], poly = arguments[1], locPtPoly = arguments[2];
				var pt = ptLoc.getCoordinate();
				if (Location.EXTERIOR !== this.ptLocator.locate(pt, poly)) {
					this.minDistance = 0.0;
					locPtPoly[0] = ptLoc;
					locPtPoly[1] = new GeometryLocation(poly, pt);

					return null;
				}
			}
		}
	},
	computeMinDistanceLinesPoints: function (lines, points, locGeom) {
		for (var i = 0; i < lines.size(); i++) {
			var line = lines.get(i);
			for (var j = 0; j < points.size(); j++) {
				var pt = points.get(j);
				this.computeMinDistance(line, pt, locGeom);
				if (this.minDistance <= this.terminateDistance) return null;
			}
		}
	},
	computeFacetDistance: function () {
		var locGeom = new Array(2).fill(null);
		var lines0 = LinearComponentExtracter.getLines(this.geom[0]);
		var lines1 = LinearComponentExtracter.getLines(this.geom[1]);
		var pts0 = PointExtracter.getPoints(this.geom[0]);
		var pts1 = PointExtracter.getPoints(this.geom[1]);
		this.computeMinDistanceLines(lines0, lines1, locGeom);
		this.updateMinDistance(locGeom, false);
		if (this.minDistance <= this.terminateDistance) return null;
		locGeom[0] = null;
		locGeom[1] = null;
		this.computeMinDistanceLinesPoints(lines0, pts1, locGeom);
		this.updateMinDistance(locGeom, false);
		if (this.minDistance <= this.terminateDistance) return null;
		locGeom[0] = null;
		locGeom[1] = null;
		this.computeMinDistanceLinesPoints(lines1, pts0, locGeom);
		this.updateMinDistance(locGeom, true);
		if (this.minDistance <= this.terminateDistance) return null;
		locGeom[0] = null;
		locGeom[1] = null;
		this.computeMinDistancePoints(pts0, pts1, locGeom);
		this.updateMinDistance(locGeom, false);
	},
	nearestLocations: function () {
		this.computeMinDistance();
		return this.minDistanceLocation;
	},
	updateMinDistance: function (locGeom, flip) {
		if (locGeom[0] === null) return null;
		if (flip) {
			this.minDistanceLocation[0] = locGeom[1];
			this.minDistanceLocation[1] = locGeom[0];
		} else {
			this.minDistanceLocation[0] = locGeom[0];
			this.minDistanceLocation[1] = locGeom[1];
		}
	},
	nearestPoints: function () {
		this.computeMinDistance();
		var nearestPts = [this.minDistanceLocation[0].getCoordinate(), this.minDistanceLocation[1].getCoordinate()];
		return nearestPts;
	},
	computeMinDistance: function () {
		if (arguments.length === 0) {
			if (this.minDistanceLocation !== null) return null;
			this.minDistanceLocation = new Array(2).fill(null);
			this.computeContainmentDistance();
			if (this.minDistance <= this.terminateDistance) return null;
			this.computeFacetDistance();
		} else if (arguments.length === 3) {
			if (arguments[2] instanceof Array && (arguments[0] instanceof LineString && arguments[1] instanceof Point)) {
				let line = arguments[0], pt = arguments[1], locGeom = arguments[2];
				if (line.getEnvelopeInternal().distance(pt.getEnvelopeInternal()) > this.minDistance) return null;
				var coord0 = line.getCoordinates();
				var coord = pt.getCoordinate();
				for (var i = 0; i < coord0.length - 1; i++) {
					var dist = CGAlgorithms.distancePointLine(coord, coord0[i], coord0[i + 1]);
					if (dist < this.minDistance) {
						this.minDistance = dist;
						var seg = new LineSegment(coord0[i], coord0[i + 1]);
						var segClosestPoint = seg.closestPoint(coord);
						locGeom[0] = new GeometryLocation(line, i, segClosestPoint);
						locGeom[1] = new GeometryLocation(pt, 0, coord);
					}
					if (this.minDistance <= this.terminateDistance) return null;
				}
			} else if (arguments[2] instanceof Array && (arguments[0] instanceof LineString && arguments[1] instanceof LineString)) {
				let line0 = arguments[0], line1 = arguments[1], locGeom = arguments[2];
				if (line0.getEnvelopeInternal().distance(line1.getEnvelopeInternal()) > this.minDistance) return null;
				var coord0 = line0.getCoordinates();
				var coord1 = line1.getCoordinates();
				for (var i = 0; i < coord0.length - 1; i++) {
					for (var j = 0; j < coord1.length - 1; j++) {
						var dist = CGAlgorithms.distanceLineLine(coord0[i], coord0[i + 1], coord1[j], coord1[j + 1]);
						if (dist < this.minDistance) {
							this.minDistance = dist;
							var seg0 = new LineSegment(coord0[i], coord0[i + 1]);
							var seg1 = new LineSegment(coord1[j], coord1[j + 1]);
							var closestPt = seg0.closestPoints(seg1);
							locGeom[0] = new GeometryLocation(line0, i, closestPt[0]);
							locGeom[1] = new GeometryLocation(line1, j, closestPt[1]);
						}
						if (this.minDistance <= this.terminateDistance) return null;
					}
				}
			}
		}
	},
	computeMinDistancePoints: function (points0, points1, locGeom) {
		for (var i = 0; i < points0.size(); i++) {
			var pt0 = points0.get(i);
			for (var j = 0; j < points1.size(); j++) {
				var pt1 = points1.get(j);
				var dist = pt0.getCoordinate().distance(pt1.getCoordinate());
				if (dist < this.minDistance) {
					this.minDistance = dist;
					locGeom[0] = new GeometryLocation(pt0, 0, pt0.getCoordinate());
					locGeom[1] = new GeometryLocation(pt1, 0, pt1.getCoordinate());
				}
				if (this.minDistance <= this.terminateDistance) return null;
			}
		}
	},
	distance: function () {
		if (this.geom[0] === null || this.geom[1] === null) throw new IllegalArgumentException("null geometries are not supported");
		if (this.geom[0].isEmpty() || this.geom[1].isEmpty()) return 0.0;
		this.computeMinDistance();
		return this.minDistance;
	},
	computeMinDistanceLines: function (lines0, lines1, locGeom) {
		for (var i = 0; i < lines0.size(); i++) {
			var line0 = lines0.get(i);
			for (var j = 0; j < lines1.size(); j++) {
				var line1 = lines1.get(j);
				this.computeMinDistance(line0, line1, locGeom);
				if (this.minDistance <= this.terminateDistance) return null;
			}
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return DistanceOp;
	}
});
DistanceOp.distance = function (g0, g1) {
	var distOp = new DistanceOp(g0, g1);
	return distOp.distance();
};
DistanceOp.isWithinDistance = function (g0, g1, distance) {
	var distOp = new DistanceOp(g0, g1, distance);
	return distOp.distance() <= distance;
};
DistanceOp.nearestPoints = function (g0, g1) {
	var distOp = new DistanceOp(g0, g1);
	return distOp.nearestPoints();
};

function GraphComponent$1() {
	this._isMarked = false;
	this._isVisited = false;
	this.data = null;
}
extend$1(GraphComponent$1.prototype, {
	setVisited: function (isVisited) {
		this._isVisited = isVisited;
	},
	isMarked: function () {
		return this._isMarked;
	},
	setData: function (data) {
		this.data = data;
	},
	getData: function () {
		return this.data;
	},
	setMarked: function (isMarked) {
		this._isMarked = isMarked;
	},
	getContext: function () {
		return this.data;
	},
	isVisited: function () {
		return this._isVisited;
	},
	setContext: function (data) {
		this.data = data;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return GraphComponent$1;
	}
});
GraphComponent$1.getComponentWithVisitedState = function (i, visitedState) {
	while (i.hasNext()) {
		var comp = i.next();
		if (comp.isVisited() === visitedState) return comp;
	}
	return null;
};
GraphComponent$1.setVisited = function (i, visited) {
	while (i.hasNext()) {
		var comp = i.next();
		comp.setVisited(visited);
	}
};
GraphComponent$1.setMarked = function (i, marked) {
	while (i.hasNext()) {
		var comp = i.next();
		comp.setMarked(marked);
	}
};

function DirectedEdge$1() {
	GraphComponent$1.apply(this);
	this.parentEdge = null;
	this.from = null;
	this.to = null;
	this.p0 = null;
	this.p1 = null;
	this.sym = null;
	this.edgeDirection = null;
	this.quadrant = null;
	this.angle = null;
	let from = arguments[0], to = arguments[1], directionPt = arguments[2], edgeDirection = arguments[3];
	this.from = from;
	this.to = to;
	this.edgeDirection = edgeDirection;
	this.p0 = from.getCoordinate();
	this.p1 = directionPt;
	var dx = this.p1.x - this.p0.x;
	var dy = this.p1.y - this.p0.y;
	this.quadrant = Quadrant.quadrant(dx, dy);
	this.angle = Math.atan2(dy, dx);
}
inherits(DirectedEdge$1, GraphComponent$1);
extend$1(DirectedEdge$1.prototype, {
	isRemoved: function () {
		return this.parentEdge === null;
	},
	compareDirection: function (e) {
		if (this.quadrant > e.quadrant) return 1;
		if (this.quadrant < e.quadrant) return -1;
		return CGAlgorithms.computeOrientation(e.p0, e.p1, this.p1);
	},
	getCoordinate: function () {
		return this.from.getCoordinate();
	},
	print: function (out) {
		var className = this.getClass().getName();
		var lastDotPos = className.lastIndexOf('.');
		var name = className.substring(lastDotPos + 1);
		out.print("  " + name + ": " + this.p0 + " - " + this.p1 + " " + this.quadrant + ":" + this.angle);
	},
	getDirectionPt: function () {
		return this.p1;
	},
	getAngle: function () {
		return this.angle;
	},
	compareTo: function (obj) {
		var de = obj;
		return this.compareDirection(de);
	},
	getFromNode: function () {
		return this.from;
	},
	getSym: function () {
		return this.sym;
	},
	setEdge: function (parentEdge) {
		this.parentEdge = parentEdge;
	},
	remove: function () {
		this.sym = null;
		this.parentEdge = null;
	},
	getEdge: function () {
		return this.parentEdge;
	},
	getQuadrant: function () {
		return this.quadrant;
	},
	setSym: function (sym) {
		this.sym = sym;
	},
	getToNode: function () {
		return this.to;
	},
	getEdgeDirection: function () {
		return this.edgeDirection;
	},
	interfaces_: function () {
		return [Comparable];
	},
	getClass: function () {
		return DirectedEdge$1;
	}
});
DirectedEdge$1.toEdges = function (dirEdges) {
	var edges = new ArrayList();
	for (var i = dirEdges.iterator(); i.hasNext(); ) {
		edges.add(i.next().parentEdge);
	}
	return edges;
};

function PolygonizeDirectedEdge() {
	this.edgeRing = null;
	this.next = null;
	this.label = -1;
	let from = arguments[0], to = arguments[1], directionPt = arguments[2], edgeDirection = arguments[3];
	DirectedEdge$1.call(this, from, to, directionPt, edgeDirection);
}
inherits(PolygonizeDirectedEdge, DirectedEdge$1);
extend$1(PolygonizeDirectedEdge.prototype, {
	getNext: function () {
		return this.next;
	},
	isInRing: function () {
		return this.edgeRing !== null;
	},
	setRing: function (edgeRing) {
		this.edgeRing = edgeRing;
	},
	setLabel: function (label) {
		this.label = label;
	},
	getLabel: function () {
		return this.label;
	},
	setNext: function (next) {
		this.next = next;
	},
	getRing: function () {
		return this.edgeRing;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return PolygonizeDirectedEdge;
	}
});

/**
 * @param {string=} message Optional message
 * @extends {Error}
 * @constructor
 * @private
 */
function EmptyStackException(message) {
  this.message = message || '';
}
EmptyStackException.prototype = new Error();


/**
 * @type {string}
 */
EmptyStackException.prototype.name = 'EmptyStackException';

/**
 * @see http://download.oracle.com/javase/6/docs/api/java/util/Stack.html
 *
 * @extends {List}
 * @constructor
 * @private
 */
function Stack() {
  /**
   * @type {Array}
   * @private
   */
  this.array_ = [];
}
Stack.prototype = new List();


/**
 * @override
 */
Stack.prototype.add = function(e) {
  this.array_.push(e);
  return true;
};


/**
 * @override
 */
Stack.prototype.get = function(index) {
  if (index < 0 || index >= this.size()) {
    throw new IndexOutOfBoundsException();
  }

  return this.array_[index];
};


/**
 * Pushes an item onto the top of this stack.
 * @param {Object} e
 * @return {Object}
 */
Stack.prototype.push = function(e) {
  this.array_.push(e);
  return e;
};


/**
 * Pushes an item onto the top of this stack.
 * @param {Object} e
 * @return {Object}
 */
Stack.prototype.pop = function(e) {
  if (this.array_.length === 0) {
    throw new EmptyStackException();
  }

  return this.array_.pop();
};


/**
 * Looks at the object at the top of this stack without removing it from the
 * stack.
 * @return {Object}
 */
Stack.prototype.peek = function() {
  if (this.array_.length === 0) {
    throw new EmptyStackException();
  }

  return this.array_[this.array_.length - 1];
};


/**
 * Tests if this stack is empty.
 * @return {boolean} true if and only if this stack contains no items; false
 *         otherwise.
 */
Stack.prototype.empty = function() {
  if (this.array_.length === 0) {
    return true;
  } else {
    return false;
  }
};


/**
 * @return {boolean}
 */
Stack.prototype.isEmpty = function() {
  return this.empty();
};


/**
 * Returns the 1-based position where an object is on this stack. If the object
 * o occurs as an item in this stack, this method returns the distance from the
 * top of the stack of the occurrence nearest the top of the stack; the topmost
 * item on the stack is considered to be at distance 1. The equals method is
 * used to compare o to the items in this stack.
 *
 * NOTE: does not currently actually use equals. (=== is used)
 *
 * @param {Object} o
 * @return {number} the 1-based position from the top of the stack where the
 *         object is located; the return value -1 indicates that the object is
 *         not on the stack.
 */
Stack.prototype.search = function(o) {
  return this.array_.indexOf(o);
};


/**
 * @return {number}
 * @export
 */
Stack.prototype.size = function() {
  return this.array_.length;
};


/**
 * @return {Array}
 */
Stack.prototype.toArray = function() {
  var array = [];

  for (var i = 0, len = this.array_.length; i < len; i++) {
    array.push(this.array_[i]);
  }

  return array;
};

function Edge$1() {
	GraphComponent$1.apply(this);
	this.dirEdge = null;
	if (arguments.length === 0) {} else if (arguments.length === 2) {
		let de0 = arguments[0], de1 = arguments[1];
		this.setDirectedEdges(de0, de1);
	}
}
inherits(Edge$1, GraphComponent$1);
extend$1(Edge$1.prototype, {
	isRemoved: function () {
		return this.dirEdge === null;
	},
	setDirectedEdges: function (de0, de1) {
		this.dirEdge = [de0, de1];
		de0.setEdge(this);
		de1.setEdge(this);
		de0.setSym(de1);
		de1.setSym(de0);
		de0.getFromNode().addOutEdge(de0);
		de1.getFromNode().addOutEdge(de1);
	},
	getDirEdge: function () {
		if (Number.isInteger(arguments[0])) {
			let i = arguments[0];
			return this.dirEdge[i];
		} else if (arguments[0] instanceof Node$1) {
			let fromNode = arguments[0];
			if (this.dirEdge[0].getFromNode() === fromNode) return this.dirEdge[0];
			if (this.dirEdge[1].getFromNode() === fromNode) return this.dirEdge[1];
			return null;
		}
	},
	remove: function () {
		this.dirEdge = null;
	},
	getOppositeNode: function (node) {
		if (this.dirEdge[0].getFromNode() === node) return this.dirEdge[0].getToNode();
		if (this.dirEdge[1].getFromNode() === node) return this.dirEdge[1].getToNode();
		return null;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Edge$1;
	}
});

function DirectedEdgeStar() {
	this.outEdges = new ArrayList();
	this.sorted = false;
}
extend$1(DirectedEdgeStar.prototype, {
	getNextEdge: function (dirEdge) {
		var i = this.getIndex(dirEdge);
		return this.outEdges.get(this.getIndex(i + 1));
	},
	getCoordinate: function () {
		var it = this.iterator();
		if (!it.hasNext()) return null;
		var e = it.next();
		return e.getCoordinate();
	},
	iterator: function () {
		this.sortEdges();
		return this.outEdges.iterator();
	},
	sortEdges: function () {
		if (!this.sorted) {
			Collections.sort(this.outEdges);
			this.sorted = true;
		}
	},
	remove: function (de) {
		this.outEdges.remove(de);
	},
	getEdges: function () {
		this.sortEdges();
		return this.outEdges;
	},
	getNextCWEdge: function (dirEdge) {
		var i = this.getIndex(dirEdge);
		return this.outEdges.get(this.getIndex(i - 1));
	},
	getIndex: function () {
		if (arguments[0] instanceof Edge$1) {
			let edge = arguments[0];
			this.sortEdges();
			for (var i = 0; i < this.outEdges.size(); i++) {
				var de = this.outEdges.get(i);
				if (de.getEdge() === edge) return i;
			}
			return -1;
		} else if (arguments[0] instanceof DirectedEdge$1) {
			let dirEdge = arguments[0];
			this.sortEdges();
			for (var i = 0; i < this.outEdges.size(); i++) {
				var de = this.outEdges.get(i);
				if (de === dirEdge) return i;
			}
			return -1;
		} else if (Number.isInteger(arguments[0])) {
			let i = arguments[0];
			var modi = i % this.outEdges.size();
			if (modi < 0) modi += this.outEdges.size();
			return modi;
		}
	},
	add: function (de) {
		this.outEdges.add(de);
		this.sorted = false;
	},
	getDegree: function () {
		return this.outEdges.size();
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return DirectedEdgeStar;
	}
});

function Node$1() {
	GraphComponent$1.apply(this);
	this.pt = null;
	this.deStar = null;
	if (arguments.length === 1) {
		let pt = arguments[0];
		Node$1.call(this, pt, new DirectedEdgeStar());
	} else if (arguments.length === 2) {
		let pt = arguments[0], deStar = arguments[1];
		this.pt = pt;
		this.deStar = deStar;
	}
}
inherits(Node$1, GraphComponent$1);
extend$1(Node$1.prototype, {
	isRemoved: function () {
		return this.pt === null;
	},
	addOutEdge: function (de) {
		this.deStar.add(de);
	},
	getCoordinate: function () {
		return this.pt;
	},
	getOutEdges: function () {
		return this.deStar;
	},
	remove: function () {
		if (arguments.length === 0) {
			this.pt = null;
		} else if (arguments.length === 1) {
			let de = arguments[0];
			this.deStar.remove(de);
		}
	},
	getIndex: function (edge) {
		return this.deStar.getIndex(edge);
	},
	getDegree: function () {
		return this.deStar.getDegree();
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Node$1;
	}
});
Node$1.getEdgesBetween = function (node0, node1) {
	var edges0 = DirectedEdge$1.toEdges(node0.getOutEdges().getEdges());
	var commonEdges = new HashSet(edges0);
	var edges1 = DirectedEdge$1.toEdges(node1.getOutEdges().getEdges());
	commonEdges.retainAll(edges1);
	return commonEdges;
};

function PolygonizeEdge() {
	Edge$1.apply(this);
	this.line = null;
	let line = arguments[0];
	this.line = line;
}
inherits(PolygonizeEdge, Edge$1);
extend$1(PolygonizeEdge.prototype, {
	getLine: function () {
		return this.line;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return PolygonizeEdge;
	}
});

function EdgeRing$1() {
	this.startDe = null;
	this.maxNodeDegree = -1;
	this.edges = new ArrayList();
	this.pts = new ArrayList();
	this.label = new Label(Location.NONE);
	this.ring = null;
	this._isHole = null;
	this.shell = null;
	this.holes = new ArrayList();
	this.geometryFactory = null;
	let start = arguments[0], geometryFactory = arguments[1];
	this.geometryFactory = geometryFactory;
	this.computePoints(start);
	this.computeRing();
}
extend$1(EdgeRing$1.prototype, {
	computeRing: function () {
		if (this.ring !== null) return null;
		var coord = new Array(this.pts.size()).fill(null);
		for (var i = 0; i < this.pts.size(); i++) {
			coord[i] = this.pts.get(i);
		}
		this.ring = this.geometryFactory.createLinearRing(coord);
		this._isHole = CGAlgorithms.isCCW(this.ring.getCoordinates());
	},
	isIsolated: function () {
		return this.label.getGeometryCount() === 1;
	},
	computePoints: function (start) {
		this.startDe = start;
		var de = start;
		var isFirstEdge = true;
		do {
			if (de === null) throw new TopologyException("Found null DirectedEdge");
			if (de.getEdgeRing() === this) throw new TopologyException("Directed Edge visited twice during ring-building at " + de.getCoordinate());
			this.edges.add(de);
			var label = de.getLabel();
			Assert.isTrue(label.isArea());
			this.mergeLabel(label);
			this.addPoints(de.getEdge(), de.isForward(), isFirstEdge);
			isFirstEdge = false;
			this.setEdgeRing(de, this);
			de = this.getNext(de);
		} while (de !== this.startDe);
	},
	getLinearRing: function () {
		return this.ring;
	},
	getCoordinate: function (i) {
		return this.pts.get(i);
	},
	computeMaxNodeDegree: function () {
		this.maxNodeDegree = 0;
		var de = this.startDe;
		do {
			var node = de.getNode();
			var degree = node.getEdges().getOutgoingDegree(this);
			if (degree > this.maxNodeDegree) this.maxNodeDegree = degree;
			de = this.getNext(de);
		} while (de !== this.startDe);
		this.maxNodeDegree *= 2;
	},
	addPoints: function (edge, isForward, isFirstEdge) {
		var edgePts = edge.getCoordinates();
		if (isForward) {
			var startIndex = 1;
			if (isFirstEdge) startIndex = 0;
			for (var i = startIndex; i < edgePts.length; i++) {
				this.pts.add(edgePts[i]);
			}
		} else {
			var startIndex = edgePts.length - 2;
			if (isFirstEdge) startIndex = edgePts.length - 1;
			for (var i = startIndex; i >= 0; i--) {
				this.pts.add(edgePts[i]);
			}
		}
	},
	isHole: function () {
		return this._isHole;
	},
	setInResult: function () {
		var de = this.startDe;
		do {
			de.getEdge().setInResult(true);
			de = de.getNext();
		} while (de !== this.startDe);
	},
	containsPoint: function (p) {
		var shell = this.getLinearRing();
		var env = shell.getEnvelopeInternal();
		if (!env.contains(p)) return false;
		if (!CGAlgorithms.isPointInRing(p, shell.getCoordinates())) return false;
		for (var i = this.holes.iterator(); i.hasNext(); ) {
			var hole = i.next();
			if (hole.containsPoint(p)) return false;
		}
		return true;
	},
	addHole: function (ring) {
		this.holes.add(ring);
	},
	isShell: function () {
		return this.shell === null;
	},
	getLabel: function () {
		return this.label;
	},
	getEdges: function () {
		return this.edges;
	},
	getMaxNodeDegree: function () {
		if (this.maxNodeDegree < 0) this.computeMaxNodeDegree();
		return this.maxNodeDegree;
	},
	getShell: function () {
		return this.shell;
	},
	mergeLabel: function () {
		if (arguments.length === 1) {
			let deLabel = arguments[0];
			this.mergeLabel(deLabel, 0);
			this.mergeLabel(deLabel, 1);
		} else if (arguments.length === 2) {
			let deLabel = arguments[0], geomIndex = arguments[1];
			var loc = deLabel.getLocation(geomIndex, Position.RIGHT);
			if (loc === Location.NONE) return null;
			if (this.label.getLocation(geomIndex) === Location.NONE) {
				this.label.setLocation(geomIndex, loc);
				return null;
			}
		}
	},
	setShell: function (shell) {
		this.shell = shell;
		if (shell !== null) shell.addHole(this);
	},
	toPolygon: function (geometryFactory) {
		var holeLR = new Array(this.holes.size()).fill(null);
		for (var i = 0; i < this.holes.size(); i++) {
			holeLR[i] = this.holes.get(i).getLinearRing();
		}
		var poly = geometryFactory.createPolygon(this.getLinearRing(), holeLR);
		return poly;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return EdgeRing$1;
	}
});

function MinimalEdgeRing() {
	let start = arguments[0], geometryFactory = arguments[1];
	EdgeRing$1.call(this, start, geometryFactory);
}
inherits(MinimalEdgeRing, EdgeRing$1);
extend$1(MinimalEdgeRing.prototype, {
	setEdgeRing: function (de, er) {
		de.setMinEdgeRing(er);
	},
	getNext: function (de) {
		return de.getNextMin();
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return MinimalEdgeRing;
	}
});

function MaximalEdgeRing() {
	let start = arguments[0], geometryFactory = arguments[1];
	EdgeRing$1.call(this, start, geometryFactory);
}
inherits(MaximalEdgeRing, EdgeRing$1);
extend$1(MaximalEdgeRing.prototype, {
	buildMinimalRings: function () {
		var minEdgeRings = new ArrayList();
		var de = this.startDe;
		do {
			if (de.getMinEdgeRing() === null) {
				var minEr = new MinimalEdgeRing(de, this.geometryFactory);
				minEdgeRings.add(minEr);
			}
			de = de.getNext();
		} while (de !== this.startDe);
		return minEdgeRings;
	},
	setEdgeRing: function (de, er) {
		de.setEdgeRing(er);
	},
	linkDirectedEdgesForMinimalEdgeRings: function () {
		var de = this.startDe;
		do {
			var node = de.getNode();
			node.getEdges().linkMinimalDirectedEdges(this);
			de = de.getNext();
		} while (de !== this.startDe);
	},
	getNext: function (de) {
		return de.getNext();
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return MaximalEdgeRing;
	}
});

function DirectedEdgeStar$1() {
	EdgeEndStar.apply(this);
	this.resultAreaEdgeList = null;
	this.label = null;
	this.SCANNING_FOR_INCOMING = 1;
	this.LINKING_TO_OUTGOING = 2;
}
inherits(DirectedEdgeStar$1, EdgeEndStar);
extend$1(DirectedEdgeStar$1.prototype, {
	linkResultDirectedEdges: function () {
		this.getResultAreaEdges();
		var firstOut = null;
		var incoming = null;
		var state = this.SCANNING_FOR_INCOMING;
		for (var i = 0; i < this.resultAreaEdgeList.size(); i++) {
			var nextOut = this.resultAreaEdgeList.get(i);
			var nextIn = nextOut.getSym();
			if (!nextOut.getLabel().isArea()) continue;
			if (firstOut === null && nextOut.isInResult()) firstOut = nextOut;
			switch (state) {
				case this.SCANNING_FOR_INCOMING:
					if (!nextIn.isInResult()) continue;
					incoming = nextIn;
					state = this.LINKING_TO_OUTGOING;
					break;
				case this.LINKING_TO_OUTGOING:
					if (!nextOut.isInResult()) continue;
					incoming.setNext(nextOut);
					state = this.SCANNING_FOR_INCOMING;
					break;
			}
		}
		if (state === this.LINKING_TO_OUTGOING) {
			if (firstOut === null) throw new TopologyException("no outgoing dirEdge found", this.getCoordinate());
			Assert.isTrue(firstOut.isInResult(), "unable to link last incoming dirEdge");
			incoming.setNext(firstOut);
		}
	},
	insert: function (ee) {
		var de = ee;
		this.insertEdgeEnd(de, de);
	},
	getRightmostEdge: function () {
		var edges = this.getEdges();
		var size = edges.size();
		if (size < 1) return null;
		var de0 = edges.get(0);
		if (size === 1) return de0;
		var deLast = edges.get(size - 1);
		var quad0 = de0.getQuadrant();
		var quad1 = deLast.getQuadrant();
		if (Quadrant.isNorthern(quad0) && Quadrant.isNorthern(quad1)) return de0; else if (!Quadrant.isNorthern(quad0) && !Quadrant.isNorthern(quad1)) return deLast; else {
			if (de0.getDy() !== 0) return de0; else if (deLast.getDy() !== 0) return deLast;
		}
		Assert.shouldNeverReachHere("found two horizontal edges incident on node");
		return null;
	},
	print: function (out) {
		System.out.println("DirectedEdgeStar: " + this.getCoordinate());
		for (var it = this.iterator(); it.hasNext(); ) {
			var de = it.next();
			out.print("out ");
			de.print(out);
			out.println();
			out.print("in ");
			de.getSym().print(out);
			out.println();
		}
	},
	getResultAreaEdges: function () {
		if (this.resultAreaEdgeList !== null) return this.resultAreaEdgeList;
		this.resultAreaEdgeList = new ArrayList();
		for (var it = this.iterator(); it.hasNext(); ) {
			var de = it.next();
			if (de.isInResult() || de.getSym().isInResult()) this.resultAreaEdgeList.add(de);
		}
		return this.resultAreaEdgeList;
	},
	updateLabelling: function (nodeLabel) {
		for (var it = this.iterator(); it.hasNext(); ) {
			var de = it.next();
			var label = de.getLabel();
			label.setAllLocationsIfNull(0, nodeLabel.getLocation(0));
			label.setAllLocationsIfNull(1, nodeLabel.getLocation(1));
		}
	},
	linkAllDirectedEdges: function () {
		this.getEdges();
		var prevOut = null;
		var firstIn = null;
		for (var i = this.edgeList.size() - 1; i >= 0; i--) {
			var nextOut = this.edgeList.get(i);
			var nextIn = nextOut.getSym();
			if (firstIn === null) firstIn = nextIn;
			if (prevOut !== null) nextIn.setNext(prevOut);
			prevOut = nextOut;
		}
		firstIn.setNext(prevOut);
	},
	computeDepths: function () {
		if (arguments.length === 1) {
			let de = arguments[0];
			var edgeIndex = this.findIndex(de);
			var label = de.getLabel();
			var startDepth = de.getDepth(Position.LEFT);
			var targetLastDepth = de.getDepth(Position.RIGHT);
			var nextDepth = this.computeDepths(edgeIndex + 1, this.edgeList.size(), startDepth);
			var lastDepth = this.computeDepths(0, edgeIndex, nextDepth);
			if (lastDepth !== targetLastDepth) throw new TopologyException("depth mismatch at " + de.getCoordinate());
		} else if (arguments.length === 3) {
			let startIndex = arguments[0], endIndex = arguments[1], startDepth = arguments[2];
			var currDepth = startDepth;
			for (var i = startIndex; i < endIndex; i++) {
				var nextDe = this.edgeList.get(i);
				var label = nextDe.getLabel();
				nextDe.setEdgeDepths(Position.RIGHT, currDepth);
				currDepth = nextDe.getDepth(Position.LEFT);
			}
			return currDepth;
		}
	},
	mergeSymLabels: function () {
		for (var it = this.iterator(); it.hasNext(); ) {
			var de = it.next();
			var label = de.getLabel();
			label.merge(de.getSym().getLabel());
		}
	},
	linkMinimalDirectedEdges: function (er) {
		var firstOut = null;
		var incoming = null;
		var state = this.SCANNING_FOR_INCOMING;
		for (var i = this.resultAreaEdgeList.size() - 1; i >= 0; i--) {
			var nextOut = this.resultAreaEdgeList.get(i);
			var nextIn = nextOut.getSym();
			if (firstOut === null && nextOut.getEdgeRing() === er) firstOut = nextOut;
			switch (state) {
				case this.SCANNING_FOR_INCOMING:
					if (nextIn.getEdgeRing() !== er) continue;
					incoming = nextIn;
					state = this.LINKING_TO_OUTGOING;
					break;
				case this.LINKING_TO_OUTGOING:
					if (nextOut.getEdgeRing() !== er) continue;
					incoming.setNextMin(nextOut);
					state = this.SCANNING_FOR_INCOMING;
					break;
			}
		}
		if (state === this.LINKING_TO_OUTGOING) {
			Assert.isTrue(firstOut !== null, "found null for first outgoing dirEdge");
			Assert.isTrue(firstOut.getEdgeRing() === er, "unable to link last incoming dirEdge");
			incoming.setNextMin(firstOut);
		}
	},
	getOutgoingDegree: function () {
		if (arguments.length === 0) {
			var degree = 0;
			for (var it = this.iterator(); it.hasNext(); ) {
				var de = it.next();
				if (de.isInResult()) degree++;
			}
			return degree;
		} else if (arguments.length === 1) {
			let er = arguments[0];
			var degree = 0;
			for (var it = this.iterator(); it.hasNext(); ) {
				var de = it.next();
				if (de.getEdgeRing() === er) degree++;
			}
			return degree;
		}
	},
	getLabel: function () {
		return this.label;
	},
	findCoveredLineEdges: function () {
		var startLoc = Location.NONE;
		for (var it = this.iterator(); it.hasNext(); ) {
			var nextOut = it.next();
			var nextIn = nextOut.getSym();
			if (!nextOut.isLineEdge()) {
				if (nextOut.isInResult()) {
					startLoc = Location.INTERIOR;
					break;
				}
				if (nextIn.isInResult()) {
					startLoc = Location.EXTERIOR;
					break;
				}
			}
		}
		if (startLoc === Location.NONE) return null;
		var currLoc = startLoc;
		for (var it = this.iterator(); it.hasNext(); ) {
			var nextOut = it.next();
			var nextIn = nextOut.getSym();
			if (nextOut.isLineEdge()) {
				nextOut.getEdge().setCovered(currLoc === Location.INTERIOR);
			} else {
				if (nextOut.isInResult()) currLoc = Location.EXTERIOR;
				if (nextIn.isInResult()) currLoc = Location.INTERIOR;
			}
		}
	},
	computeLabelling: function (geom) {
		EdgeEndStar.prototype.computeLabelling.call(this, geom);
		this.label = new Label(Location.NONE);
		for (var it = this.iterator(); it.hasNext(); ) {
			var ee = it.next();
			var e = ee.getEdge();
			var eLabel = e.getLabel();
			for (var i = 0; i < 2; i++) {
				var eLoc = eLabel.getLocation(i);
				if (eLoc === Location.INTERIOR || eLoc === Location.BOUNDARY) this.label.setLocation(i, Location.INTERIOR);
			}
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return DirectedEdgeStar$1;
	}
});

function OverlayNodeFactory() {
	NodeFactory.apply(this);
}
inherits(OverlayNodeFactory, NodeFactory);
extend$1(OverlayNodeFactory.prototype, {
	createNode: function (coord) {
		return new Node(coord, new DirectedEdgeStar$1());
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return OverlayNodeFactory;
	}
});

function ConnectedInteriorTester() {
	this.geometryFactory = new GeometryFactory();
	this.geomGraph = null;
	this.disconnectedRingcoord = null;
	let geomGraph = arguments[0];
	this.geomGraph = geomGraph;
}
extend$1(ConnectedInteriorTester.prototype, {
	visitInteriorRing: function (ring, graph) {
		var pts = ring.getCoordinates();
		var pt0 = pts[0];
		var pt1 = ConnectedInteriorTester.findDifferentPoint(pts, pt0);
		var e = graph.findEdgeInSameDirection(pt0, pt1);
		var de = graph.findEdgeEnd(e);
		var intDe = null;
		if (de.getLabel().getLocation(0, Position.RIGHT) === Location.INTERIOR) {
			intDe = de;
		} else if (de.getSym().getLabel().getLocation(0, Position.RIGHT) === Location.INTERIOR) {
			intDe = de.getSym();
		}
		Assert.isTrue(intDe !== null, "unable to find dirEdge with Interior on RHS");
		this.visitLinkedDirectedEdges(intDe);
	},
	visitShellInteriors: function (g, graph) {
		if (g instanceof Polygon) {
			var p = g;
			this.visitInteriorRing(p.getExteriorRing(), graph);
		}
		if (g instanceof MultiPolygon) {
			var mp = g;
			for (var i = 0; i < mp.getNumGeometries(); i++) {
				var p = mp.getGeometryN(i);
				this.visitInteriorRing(p.getExteriorRing(), graph);
			}
		}
	},
	getCoordinate: function () {
		return this.disconnectedRingcoord;
	},
	setInteriorEdgesInResult: function (graph) {
		for (var it = graph.getEdgeEnds().iterator(); it.hasNext(); ) {
			var de = it.next();
			if (de.getLabel().getLocation(0, Position.RIGHT) === Location.INTERIOR) {
				de.setInResult(true);
			}
		}
	},
	visitLinkedDirectedEdges: function (start) {
		var startDe = start;
		var de = start;
		do {
			Assert.isTrue(de !== null, "found null Directed Edge");
			de.setVisited(true);
			de = de.getNext();
		} while (de !== startDe);
	},
	buildEdgeRings: function (dirEdges) {
		var edgeRings = new ArrayList();
		for (var it = dirEdges.iterator(); it.hasNext(); ) {
			var de = it.next();
			if (de.isInResult() && de.getEdgeRing() === null) {
				var er = new MaximalEdgeRing(de, this.geometryFactory);
				er.linkDirectedEdgesForMinimalEdgeRings();
				var minEdgeRings = er.buildMinimalRings();
				edgeRings.addAll(minEdgeRings);
			}
		}
		return edgeRings;
	},
	hasUnvisitedShellEdge: function (edgeRings) {
		for (var i = 0; i < edgeRings.size(); i++) {
			var er = edgeRings.get(i);
			if (er.isHole()) continue;
			var edges = er.getEdges();
			var de = edges.get(0);
			if (de.getLabel().getLocation(0, Position.RIGHT) !== Location.INTERIOR) continue;
			for (var j = 0; j < edges.size(); j++) {
				de = edges.get(j);
				if (!de.isVisited()) {
					this.disconnectedRingcoord = de.getCoordinate();
					return true;
				}
			}
		}
		return false;
	},
	isInteriorsConnected: function () {
		var splitEdges = new ArrayList();
		this.geomGraph.computeSplitEdges(splitEdges);
		var graph = new PlanarGraph(new OverlayNodeFactory());
		graph.addEdges(splitEdges);
		this.setInteriorEdgesInResult(graph);
		graph.linkResultDirectedEdges();
		var edgeRings = this.buildEdgeRings(graph.getEdgeEnds());
		this.visitShellInteriors(this.geomGraph.getGeometry(), graph);
		return !this.hasUnvisitedShellEdge(edgeRings);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return ConnectedInteriorTester;
	}
});
ConnectedInteriorTester.findDifferentPoint = function (coord, pt) {
	for (var i = 0; i < coord.length; i++) {
		if (!coord[i].equals(pt)) return coord[i];
	}
	return null;
};

function MonotoneChainSelectAction() {
	this.tempEnv1 = new Envelope();
	this.selectedSegment = new LineSegment();
}
extend$1(MonotoneChainSelectAction.prototype, {
	select: function () {
		if (arguments.length === 1) {

		} else if (arguments.length === 2) {
			let mc = arguments[0], startIndex = arguments[1];
			mc.getLineSegment(startIndex, this.selectedSegment);
			this.select(this.selectedSegment);
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return MonotoneChainSelectAction;
	}
});

function NodeBase() {
	this.items = new ArrayList();
	this.subnode = [null, null];
}
extend$1(NodeBase.prototype, {
	hasChildren: function () {
		for (var i = 0; i < 2; i++) {
			if (this.subnode[i] !== null) return true;
		}
		return false;
	},
	isPrunable: function () {
		return !(this.hasChildren() || this.hasItems());
	},
	addAllItems: function (items) {
		items.addAll(this.items);
		for (var i = 0; i < 2; i++) {
			if (this.subnode[i] !== null) {
				this.subnode[i].addAllItems(items);
			}
		}
		return items;
	},
	size: function () {
		var subSize = 0;
		for (var i = 0; i < 2; i++) {
			if (this.subnode[i] !== null) {
				subSize += this.subnode[i].size();
			}
		}
		return subSize + this.items.size();
	},
	addAllItemsFromOverlapping: function (interval, resultItems) {
		if (interval !== null && !this.isSearchMatch(interval)) return null;
		resultItems.addAll(this.items);
		if (this.subnode[0] !== null) this.subnode[0].addAllItemsFromOverlapping(interval, resultItems);
		if (this.subnode[1] !== null) this.subnode[1].addAllItemsFromOverlapping(interval, resultItems);
	},
	hasItems: function () {
		return !this.items.isEmpty();
	},
	remove: function (itemInterval, item) {
		if (!this.isSearchMatch(itemInterval)) return false;
		var found = false;
		for (var i = 0; i < 2; i++) {
			if (this.subnode[i] !== null) {
				found = this.subnode[i].remove(itemInterval, item);
				if (found) {
					if (this.subnode[i].isPrunable()) this.subnode[i] = null;
					break;
				}
			}
		}
		if (found) return found;
		found = this.items.remove(item);
		return found;
	},
	getItems: function () {
		return this.items;
	},
	depth: function () {
		var maxSubDepth = 0;
		for (var i = 0; i < 2; i++) {
			if (this.subnode[i] !== null) {
				var sqd = this.subnode[i].depth();
				if (sqd > maxSubDepth) maxSubDepth = sqd;
			}
		}
		return maxSubDepth + 1;
	},
	nodeSize: function () {
		var subSize = 0;
		for (var i = 0; i < 2; i++) {
			if (this.subnode[i] !== null) {
				subSize += this.subnode[i].nodeSize();
			}
		}
		return subSize + 1;
	},
	add: function (item) {
		this.items.add(item);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return NodeBase;
	}
});
NodeBase.getSubnodeIndex = function (interval, centre) {
	var subnodeIndex = -1;
	if (interval.min >= centre) subnodeIndex = 1;
	if (interval.max <= centre) subnodeIndex = 0;
	return subnodeIndex;
};

function Interval() {
	this.min = null;
	this.max = null;
	if (arguments.length === 0) {
		this.min = 0.0;
		this.max = 0.0;
	} else if (arguments.length === 1) {
		let interval = arguments[0];
		this.init(interval.min, interval.max);
	} else if (arguments.length === 2) {
		let min = arguments[0], max = arguments[1];
		this.init(min, max);
	}
}
extend$1(Interval.prototype, {
	expandToInclude: function (interval) {
		if (interval.max > this.max) this.max = interval.max;
		if (interval.min < this.min) this.min = interval.min;
	},
	getWidth: function () {
		return this.max - this.min;
	},
	overlaps: function () {
		if (arguments.length === 1) {
			let interval = arguments[0];
			return this.overlaps(interval.min, interval.max);
		} else if (arguments.length === 2) {
			let min = arguments[0], max = arguments[1];
			if (this.min > max || this.max < min) return false;
			return true;
		}
	},
	getMin: function () {
		return this.min;
	},
	toString: function () {
		return "[" + this.min + ", " + this.max + "]";
	},
	contains: function () {
		if (arguments.length === 1) {
			if (arguments[0] instanceof Interval) {
				let interval = arguments[0];
				return this.contains(interval.min, interval.max);
			} else if (typeof arguments[0] === "number") {
				let p = arguments[0];
				return p >= this.min && p <= this.max;
			}
		} else if (arguments.length === 2) {
			let min = arguments[0], max = arguments[1];
			return min >= this.min && max <= this.max;
		}
	},
	init: function (min, max) {
		this.min = min;
		this.max = max;
		if (min > max) {
			this.min = max;
			this.max = min;
		}
	},
	getMax: function () {
		return this.max;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Interval;
	}
});

function DoubleBits () { }
DoubleBits.exponent = function (d) {
  return CVTFWD(64, d) - 1023
};
DoubleBits.powerOf2 = function (exp) {
  return Math.pow(2, exp)
};

/**
 * Calculates the exponent of the bit-pattern for a number. Uses code from:
 * http://www.merlyn.demon.co.uk/js-exact.htm
 *
 * @param {Number}
 *          NumW 32 or 64 to denote the number of bits.
 * @param {Number}
 *          Qty the number to calculate the bit pattern for.
 * @return {Number} The integer value of the exponent.
 */
function CVTFWD (NumW, Qty) {
  var Sign;
  var Expo;
  var Mant;
  var Bin;
  var Inf = {
    32: {
      d: 0x7F,
      c: 0x80,
      b: 0,
      a: 0
    },
    64: {
      d: 0x7FF0,
      c: 0,
      b: 0,
      a: 0
    }
  };
  var ExW = {
    32: 8,
    64: 11
  }[NumW];

  if (!Bin) {
    Sign = Qty < 0 || 1 / Qty < 0; // OK for +-0
    if (!isFinite(Qty)) {
      Bin = Inf[NumW];
      if (Sign) {
        Bin.d += 1 << (NumW / 4 - 1);
      }
      Expo = Math.pow(2, ExW) - 1;
      Mant = 0;
    }
  }

  if (!Bin) {
    Expo = {
      32: 127,
      64: 1023
    }[NumW];
    Mant = Math.abs(Qty);
    while (Mant >= 2) {
      Expo++;
      Mant /= 2;
    }
    while (Mant < 1 && Expo > 0) {
      Expo--;
      Mant *= 2;
    }
    if (Expo <= 0) {
      Mant /= 2;
    }
    if (NumW === 32 && Expo > 254) {
      Bin = {
        d: Sign ? 0xFF : 0x7F,
        c: 0x80,
        b: 0,
        a: 0
      };
      Expo = Math.pow(2, ExW) - 1;
      Mant = 0;
    }
  }

  return Expo
}

function Key() {
	this.pt = 0.0;
	this.level = 0;
	this.interval = null;
	let interval = arguments[0];
	this.computeKey(interval);
}
extend$1(Key.prototype, {
	getInterval: function () {
		return this.interval;
	},
	getLevel: function () {
		return this.level;
	},
	computeKey: function (itemInterval) {
		this.level = Key.computeLevel(itemInterval);
		this.interval = new Interval();
		this.computeInterval(this.level, itemInterval);
		while (!this.interval.contains(itemInterval)) {
			this.level += 1;
			this.computeInterval(this.level, itemInterval);
		}
	},
	computeInterval: function (level, itemInterval) {
		var size = DoubleBits.powerOf2(level);
		this.pt = Math.floor(itemInterval.getMin() / size) * size;
		this.interval.init(this.pt, this.pt + size);
	},
	getPoint: function () {
		return this.pt;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Key;
	}
});
Key.computeLevel = function (interval) {
	var dx = interval.getWidth();
	var level = DoubleBits.exponent(dx) + 1;
	return level;
};

function Node$2() {
	NodeBase.apply(this);
	this.interval = null;
	this.centre = null;
	this.level = null;
	let interval = arguments[0], level = arguments[1];
	this.interval = interval;
	this.level = level;
	this.centre = (interval.getMin() + interval.getMax()) / 2;
}
inherits(Node$2, NodeBase);
extend$1(Node$2.prototype, {
	getInterval: function () {
		return this.interval;
	},
	find: function (searchInterval) {
		var subnodeIndex = NodeBase.getSubnodeIndex(searchInterval, this.centre);
		if (subnodeIndex === -1) return this;
		if (this.subnode[subnodeIndex] !== null) {
			var node = this.subnode[subnodeIndex];
			return node.find(searchInterval);
		}
		return this;
	},
	insert: function (node) {
		Assert.isTrue(this.interval === null || this.interval.contains(node.interval));
		var index = NodeBase.getSubnodeIndex(node.interval, this.centre);
		if (node.level === this.level - 1) {
			this.subnode[index] = node;
		} else {
			var childNode = this.createSubnode(index);
			childNode.insert(node);
			this.subnode[index] = childNode;
		}
	},
	isSearchMatch: function (itemInterval) {
		return itemInterval.overlaps(this.interval);
	},
	getSubnode: function (index) {
		if (this.subnode[index] === null) {
			this.subnode[index] = this.createSubnode(index);
		}
		return this.subnode[index];
	},
	getNode: function (searchInterval) {
		var subnodeIndex = NodeBase.getSubnodeIndex(searchInterval, this.centre);
		if (subnodeIndex !== -1) {
			var node = this.getSubnode(subnodeIndex);
			return node.getNode(searchInterval);
		} else {
			return this;
		}
	},
	createSubnode: function (index) {
		var min = 0.0;
		var max = 0.0;
		switch (index) {
			case 0:
				min = this.interval.getMin();
				max = this.centre;
				break;
			case 1:
				min = this.centre;
				max = this.interval.getMax();
				break;
		}
		var subInt = new Interval(min, max);
		var node = new Node$2(subInt, this.level - 1);
		return node;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Node$2;
	}
});
Node$2.createNode = function (itemInterval) {
	var key = new Key(itemInterval);
	var node = new Node$2(key.getInterval(), key.getLevel());
	return node;
};
Node$2.createExpanded = function (node, addInterval) {
	var expandInt = new Interval(addInterval);
	if (node !== null) expandInt.expandToInclude(node.interval);
	var largerNode = Node$2.createNode(expandInt);
	if (node !== null) largerNode.insert(node);
	return largerNode;
};

function IntervalSize() {}
extend$1(IntervalSize.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return IntervalSize;
	}
});
IntervalSize.isZeroWidth = function (min, max) {
	var width = max - min;
	if (width === 0.0) return true;
	var maxAbs = Math.max(Math.abs(min), Math.abs(max));
	var scaledInterval = width / maxAbs;
	var level = DoubleBits.exponent(scaledInterval);
	return level <= IntervalSize.MIN_BINARY_EXPONENT;
};
IntervalSize.MIN_BINARY_EXPONENT = -50;

function Root() {
	NodeBase.apply(this);
}
inherits(Root, NodeBase);
extend$1(Root.prototype, {
	insert: function (itemInterval, item) {
		var index = NodeBase.getSubnodeIndex(itemInterval, Root.origin);
		if (index === -1) {
			this.add(item);
			return null;
		}
		var node = this.subnode[index];
		if (node === null || !node.getInterval().contains(itemInterval)) {
			var largerNode = Node$2.createExpanded(node, itemInterval);
			this.subnode[index] = largerNode;
		}
		this.insertContained(this.subnode[index], itemInterval, item);
	},
	isSearchMatch: function (interval) {
		return true;
	},
	insertContained: function (tree, itemInterval, item) {
		Assert.isTrue(tree.getInterval().contains(itemInterval));
		var isZeroArea = IntervalSize.isZeroWidth(itemInterval.getMin(), itemInterval.getMax());
		var node = null;
		if (isZeroArea) node = tree.find(itemInterval); else node = tree.getNode(itemInterval);
		node.add(item);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Root;
	}
});
Root.origin = 0.0;

function Bintree() {
	this.root = null;
	this.minExtent = 1.0;
	this.root = new Root();
}
extend$1(Bintree.prototype, {
	size: function () {
		if (this.root !== null) return this.root.size();
		return 0;
	},
	insert: function (itemInterval, item) {
		this.collectStats(itemInterval);
		var insertInterval = Bintree.ensureExtent(itemInterval, this.minExtent);
		this.root.insert(insertInterval, item);
	},
	query: function () {
		if (arguments.length === 1) {
			if (typeof arguments[0] === "number") {
				let x = arguments[0];
				return this.query(new Interval(x, x));
			} else if (arguments[0] instanceof Interval) {
				let interval = arguments[0];
				var foundItems = new ArrayList();
				this.query(interval, foundItems);
				return foundItems;
			}
		} else if (arguments.length === 2) {
			let interval = arguments[0], foundItems = arguments[1];
			this.root.addAllItemsFromOverlapping(interval, foundItems);
		}
	},
	iterator: function () {
		var foundItems = new ArrayList();
		this.root.addAllItems(foundItems);
		return foundItems.iterator();
	},
	remove: function (itemInterval, item) {
		var insertInterval = Bintree.ensureExtent(itemInterval, this.minExtent);
		return this.root.remove(insertInterval, item);
	},
	collectStats: function (interval) {
		var del = interval.getWidth();
		if (del < this.minExtent && del > 0.0) this.minExtent = del;
	},
	depth: function () {
		if (this.root !== null) return this.root.depth();
		return 0;
	},
	nodeSize: function () {
		if (this.root !== null) return this.root.nodeSize();
		return 0;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Bintree;
	}
});
Bintree.ensureExtent = function (itemInterval, minExtent) {
	var min = itemInterval.getMin();
	var max = itemInterval.getMax();
	if (min !== max) return itemInterval;
	if (min === max) {
		min = min - minExtent / 2.0;
		max = min + minExtent / 2.0;
	}
	return new Interval(min, max);
};

function MonotoneChain$1() {
	this.pts = null;
	this.start = null;
	this.end = null;
	this.env = null;
	this.context = null;
	this.id = null;
	let pts = arguments[0], start = arguments[1], end = arguments[2], context = arguments[3];
	this.pts = pts;
	this.start = start;
	this.end = end;
	this.context = context;
}
extend$1(MonotoneChain$1.prototype, {
	getLineSegment: function (index, ls) {
		ls.p0 = this.pts[index];
		ls.p1 = this.pts[index + 1];
	},
	computeSelect: function (searchEnv, start0, end0, mcs) {
		var p0 = this.pts[start0];
		var p1 = this.pts[end0];
		mcs.tempEnv1.init(p0, p1);
		if (end0 - start0 === 1) {
			mcs.select(this, start0);
			return null;
		}
		if (!searchEnv.intersects(mcs.tempEnv1)) return null;
		var mid = Math.trunc((start0 + end0) / 2);
		if (start0 < mid) {
			this.computeSelect(searchEnv, start0, mid, mcs);
		}
		if (mid < end0) {
			this.computeSelect(searchEnv, mid, end0, mcs);
		}
	},
	getCoordinates: function () {
		var coord = new Array(this.end - this.start + 1).fill(null);
		var index = 0;
		for (var i = this.start; i <= this.end; i++) {
			coord[index++] = this.pts[i];
		}
		return coord;
	},
	computeOverlaps: function (mc, mco) {
		this.computeOverlapsInternal(this.start, this.end, mc, mc.start, mc.end, mco);
	},
	setId: function (id) {
		this.id = id;
	},
	select: function (searchEnv, mcs) {
		this.computeSelect(searchEnv, this.start, this.end, mcs);
	},
	getEnvelope: function () {
		if (this.env === null) {
			var p0 = this.pts[this.start];
			var p1 = this.pts[this.end];
			this.env = new Envelope(p0, p1);
		}
		return this.env;
	},
	getEndIndex: function () {
		return this.end;
	},
	getStartIndex: function () {
		return this.start;
	},
	getContext: function () {
		return this.context;
	},
	getId: function () {
		return this.id;
	},
	computeOverlapsInternal: function (start0, end0, mc, start1, end1, mco) {
		var p00 = this.pts[start0];
		var p01 = this.pts[end0];
		var p10 = mc.pts[start1];
		var p11 = mc.pts[end1];
		if (end0 - start0 === 1 && end1 - start1 === 1) {
			mco.overlap(this, start0, mc, start1);
			return null;
		}
		mco.tempEnv1.init(p00, p01);
		mco.tempEnv2.init(p10, p11);
		if (!mco.tempEnv1.intersects(mco.tempEnv2)) return null;
		var mid0 = Math.trunc((start0 + end0) / 2);
		var mid1 = Math.trunc((start1 + end1) / 2);
		if (start0 < mid0) {
			if (start1 < mid1) this.computeOverlapsInternal(start0, mid0, mc, start1, mid1, mco);
			if (mid1 < end1) this.computeOverlapsInternal(start0, mid0, mc, mid1, end1, mco);
		}
		if (mid0 < end0) {
			if (start1 < mid1) this.computeOverlapsInternal(mid0, end0, mc, start1, mid1, mco);
			if (mid1 < end1) this.computeOverlapsInternal(mid0, end0, mc, mid1, end1, mco);
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return MonotoneChain$1;
	}
});

function MonotoneChainBuilder() {}
extend$1(MonotoneChainBuilder.prototype, {
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return MonotoneChainBuilder;
	}
});
MonotoneChainBuilder.getChainStartIndices = function (pts) {
	var start = 0;
	var startIndexList = new ArrayList();
	startIndexList.add(new Integer(start));
	do {
		var last = MonotoneChainBuilder.findChainEnd(pts, start);
		startIndexList.add(new Integer(last));
		start = last;
	} while (start < pts.length - 1);
	var startIndex = MonotoneChainBuilder.toIntArray(startIndexList);
	return startIndex;
};
MonotoneChainBuilder.findChainEnd = function (pts, start) {
	var safeStart = start;
	while (safeStart < pts.length - 1 && pts[safeStart].equals2D(pts[safeStart + 1])) {
		safeStart++;
	}
	if (safeStart >= pts.length - 1) {
		return pts.length - 1;
	}
	var chainQuad = Quadrant.quadrant(pts[safeStart], pts[safeStart + 1]);
	var last = start + 1;
	while (last < pts.length) {
		if (!pts[last - 1].equals2D(pts[last])) {
			var quad = Quadrant.quadrant(pts[last - 1], pts[last]);
			if (quad !== chainQuad) break;
		}
		last++;
	}
	return last - 1;
};
MonotoneChainBuilder.getChains = function () {
	if (arguments.length === 1) {
		let pts = arguments[0];
		return MonotoneChainBuilder.getChains(pts, null);
	} else if (arguments.length === 2) {
		let pts = arguments[0], context = arguments[1];
		var mcList = new ArrayList();
		var startIndex = MonotoneChainBuilder.getChainStartIndices(pts);
		for (var i = 0; i < startIndex.length - 1; i++) {
			var mc = new MonotoneChain$1(pts, startIndex[i], startIndex[i + 1], context);
			mcList.add(mc);
		}
		return mcList;
	}
};
MonotoneChainBuilder.toIntArray = function (list) {
	var array = new Array(list.size()).fill(null);
	for (var i = 0; i < array.length; i++) {
		array[i] = list.get(i).intValue();
	}
	return array;
};

function PointInRing() {}
extend$1(PointInRing.prototype, {
	isInside: function (pt) {},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return PointInRing;
	}
});

function MCPointInRing() {
	this.ring = null;
	this.tree = null;
	this.crossings = 0;
	this.interval = new Interval();
	let ring = arguments[0];
	this.ring = ring;
	this.buildIndex();
}
extend$1(MCPointInRing.prototype, {
	testLineSegment: function (p, seg) {
		var xInt = null;
		var x1 = null;
		var y1 = null;
		var x2 = null;
		var y2 = null;
		var p1 = seg.p0;
		var p2 = seg.p1;
		x1 = p1.x - p.x;
		y1 = p1.y - p.y;
		x2 = p2.x - p.x;
		y2 = p2.y - p.y;
		if (y1 > 0 && y2 <= 0 || y2 > 0 && y1 <= 0) {
			xInt = RobustDeterminant.signOfDet2x2(x1, y1, x2, y2) / (y2 - y1);
			if (0.0 < xInt) {
				this.crossings++;
			}
		}
	},
	buildIndex: function () {
		this.tree = new Bintree();
		var pts = CoordinateArrays.removeRepeatedPoints(this.ring.getCoordinates());
		var mcList = MonotoneChainBuilder.getChains(pts);
		for (var i = 0; i < mcList.size(); i++) {
			var mc = mcList.get(i);
			var mcEnv = mc.getEnvelope();
			this.interval.min = mcEnv.getMinY();
			this.interval.max = mcEnv.getMaxY();
			this.tree.insert(this.interval, mc);
		}
	},
	testMonotoneChain: function (rayEnv, mcSelecter, mc) {
		mc.select(rayEnv, mcSelecter);
	},
	isInside: function (pt) {
		this.crossings = 0;
		var rayEnv = new Envelope(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, pt.y, pt.y);
		this.interval.min = pt.y;
		this.interval.max = pt.y;
		var segs = this.tree.query(this.interval);
		var mcSelecter = new MCSelecter(this, pt);
		for (var i = segs.iterator(); i.hasNext(); ) {
			var mc = i.next();
			this.testMonotoneChain(rayEnv, mcSelecter, mc);
		}
		if (this.crossings % 2 === 1) {
			return true;
		}
		return false;
	},
	interfaces_: function () {
		return [PointInRing];
	},
	getClass: function () {
		return MCPointInRing;
	}
});
function MCSelecter() {
	MonotoneChainSelectAction.apply(this);
	this.mcp = null;
	this.p = null;
	let mcp = arguments[0], p = arguments[1];
	this.mcp = mcp;
	this.p = p;
}
inherits(MCSelecter, MonotoneChainSelectAction);
extend$1(MCSelecter.prototype, {
	select: function () {
		if (arguments.length === 1) {
			let ls = arguments[0];
			this.mcp.testLineSegment(this.p, ls);
		} else return MonotoneChainSelectAction.prototype.select.apply(this, arguments);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return MCSelecter;
	}
});
MCPointInRing.MCSelecter = MCSelecter;

function RelateNodeGraph() {
	this.nodes = new NodeMap(new RelateNodeFactory());
}
extend$1(RelateNodeGraph.prototype, {
	insertEdgeEnds: function (ee) {
		for (var i = ee.iterator(); i.hasNext(); ) {
			var e = i.next();
			this.nodes.add(e);
		}
	},
	getNodeIterator: function () {
		return this.nodes.iterator();
	},
	copyNodesAndLabels: function (geomGraph, argIndex) {
		for (var nodeIt = geomGraph.getNodeIterator(); nodeIt.hasNext(); ) {
			var graphNode = nodeIt.next();
			var newNode = this.nodes.addNode(graphNode.getCoordinate());
			newNode.setLabel(argIndex, graphNode.getLabel().getLocation(argIndex));
		}
	},
	build: function (geomGraph) {
		this.computeIntersectionNodes(geomGraph, 0);
		this.copyNodesAndLabels(geomGraph, 0);
		var eeBuilder = new EdgeEndBuilder();
		var eeList = eeBuilder.computeEdgeEnds(geomGraph.getEdgeIterator());
		this.insertEdgeEnds(eeList);
	},
	computeIntersectionNodes: function (geomGraph, argIndex) {
		for (var edgeIt = geomGraph.getEdgeIterator(); edgeIt.hasNext(); ) {
			var e = edgeIt.next();
			var eLoc = e.getLabel().getLocation(argIndex);
			for (var eiIt = e.getEdgeIntersectionList().iterator(); eiIt.hasNext(); ) {
				var ei = eiIt.next();
				var n = this.nodes.addNode(ei.coord);
				if (eLoc === Location.BOUNDARY) n.setLabelBoundary(argIndex); else {
					if (n.getLabel().isNull(argIndex)) n.setLabel(argIndex, Location.INTERIOR);
				}
			}
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return RelateNodeGraph;
	}
});

function ConsistentAreaTester() {
	this.li = new RobustLineIntersector();
	this.geomGraph = null;
	this.nodeGraph = new RelateNodeGraph();
	this.invalidPoint = null;
	let geomGraph = arguments[0];
	this.geomGraph = geomGraph;
}
extend$1(ConsistentAreaTester.prototype, {
	isNodeEdgeAreaLabelsConsistent: function () {
		for (var nodeIt = this.nodeGraph.getNodeIterator(); nodeIt.hasNext(); ) {
			var node = nodeIt.next();
			if (!node.getEdges().isAreaLabelsConsistent(this.geomGraph)) {
				this.invalidPoint = node.getCoordinate().copy();
				return false;
			}
		}
		return true;
	},
	getInvalidPoint: function () {
		return this.invalidPoint;
	},
	hasDuplicateRings: function () {
		for (var nodeIt = this.nodeGraph.getNodeIterator(); nodeIt.hasNext(); ) {
			var node = nodeIt.next();
			for (var i = node.getEdges().iterator(); i.hasNext(); ) {
				var eeb = i.next();
				if (eeb.getEdgeEnds().size() > 1) {
					this.invalidPoint = eeb.getEdge().getCoordinate(0);
					return true;
				}
			}
		}
		return false;
	},
	isNodeConsistentArea: function () {
		var intersector = this.geomGraph.computeSelfNodes(this.li, true, true);
		if (intersector.hasProperIntersection()) {
			this.invalidPoint = intersector.getProperIntersectionPoint();
			return false;
		}
		this.nodeGraph.build(this.geomGraph);
		return this.isNodeEdgeAreaLabelsConsistent();
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return ConsistentAreaTester;
	}
});

function Boundable() {}
extend$1(Boundable.prototype, {
	getBounds: function () {},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Boundable;
	}
});

function ItemBoundable() {
	this.bounds = null;
	this.item = null;
	let bounds = arguments[0], item = arguments[1];
	this.bounds = bounds;
	this.item = item;
}
extend$1(ItemBoundable.prototype, {
	getItem: function () {
		return this.item;
	},
	getBounds: function () {
		return this.bounds;
	},
	interfaces_: function () {
		return [Boundable, Serializable];
	},
	getClass: function () {
		return ItemBoundable;
	}
});

function PriorityQueue() {
	this._size = null;
	this.items = null;
	this._size = 0;
	this.items = new ArrayList();
	this.items.add(null);
}
extend$1(PriorityQueue.prototype, {
	poll: function () {
		if (this.isEmpty()) return null;
		var minItem = this.items.get(1);
		this.items.set(1, this.items.get(this._size));
		this._size -= 1;
		this.reorder(1);
		return minItem;
	},
	size: function () {
		return this._size;
	},
	reorder: function (hole) {
		var child = null;
		var tmp = this.items.get(hole);
		for (; hole * 2 <= this._size; hole = child) {
			child = hole * 2;
			if (child !== this._size && this.items.get(child + 1).compareTo(this.items.get(child)) < 0) child++;
			if (this.items.get(child).compareTo(tmp) < 0) this.items.set(hole, this.items.get(child)); else break;
		}
		this.items.set(hole, tmp);
	},
	clear: function () {
		this._size = 0;
		this.items.clear();
	},
	isEmpty: function () {
		return this._size === 0;
	},
	add: function (x) {
		this.items.add(null);
		this._size += 1;
		var hole = this._size;
		this.items.set(0, x);
		for (; x.compareTo(this.items.get(Math.trunc(hole / 2))) < 0; hole /= 2) {
			this.items.set(hole, this.items.get(Math.trunc(hole / 2)));
		}
		this.items.set(hole, x);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return PriorityQueue;
	}
});

function SpatialIndex() {}
extend$1(SpatialIndex.prototype, {
	insert: function (itemEnv, item) {},
	remove: function (itemEnv, item) {},
	query: function () {

	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return SpatialIndex;
	}
});

function AbstractNode() {
	this.childBoundables = new ArrayList();
	this.bounds = null;
	this.level = null;
	if (arguments.length === 0) {} else if (arguments.length === 1) {
		let level = arguments[0];
		this.level = level;
	}
}
extend$1(AbstractNode.prototype, {
	getLevel: function () {
		return this.level;
	},
	size: function () {
		return this.childBoundables.size();
	},
	getChildBoundables: function () {
		return this.childBoundables;
	},
	addChildBoundable: function (childBoundable) {
		Assert.isTrue(this.bounds === null);
		this.childBoundables.add(childBoundable);
	},
	isEmpty: function () {
		return this.childBoundables.isEmpty();
	},
	getBounds: function () {
		if (this.bounds === null) {
			this.bounds = this.computeBounds();
		}
		return this.bounds;
	},
	interfaces_: function () {
		return [Boundable, Serializable];
	},
	getClass: function () {
		return AbstractNode;
	}
});
AbstractNode.serialVersionUID = 6493722185909573708;

function BoundablePair() {
	this.boundable1 = null;
	this.boundable2 = null;
	this._distance = null;
	this.itemDistance = null;
	let boundable1 = arguments[0], boundable2 = arguments[1], itemDistance = arguments[2];
	this.boundable1 = boundable1;
	this.boundable2 = boundable2;
	this.itemDistance = itemDistance;
	this._distance = this.distance();
}
extend$1(BoundablePair.prototype, {
	expandToQueue: function (priQ, minDistance) {
		var isComp1 = BoundablePair.isComposite(this.boundable1);
		var isComp2 = BoundablePair.isComposite(this.boundable2);
		if (isComp1 && isComp2) {
			if (BoundablePair.area(this.boundable1) > BoundablePair.area(this.boundable2)) {
				this.expand(this.boundable1, this.boundable2, priQ, minDistance);
				return null;
			} else {
				this.expand(this.boundable2, this.boundable1, priQ, minDistance);
				return null;
			}
		} else if (isComp1) {
			this.expand(this.boundable1, this.boundable2, priQ, minDistance);
			return null;
		} else if (isComp2) {
			this.expand(this.boundable2, this.boundable1, priQ, minDistance);
			return null;
		}
		throw new IllegalArgumentException("neither boundable is composite");
	},
	isLeaves: function () {
		return !(BoundablePair.isComposite(this.boundable1) || BoundablePair.isComposite(this.boundable2));
	},
	compareTo: function (o) {
		var nd = o;
		if (this._distance < nd._distance) return -1;
		if (this._distance > nd._distance) return 1;
		return 0;
	},
	expand: function (bndComposite, bndOther, priQ, minDistance) {
		var children = bndComposite.getChildBoundables();
		for (var i = children.iterator(); i.hasNext(); ) {
			var child = i.next();
			var bp = new BoundablePair(child, bndOther, this.itemDistance);
			if (bp.getDistance() < minDistance) {
				priQ.add(bp);
			}
		}
	},
	getBoundable: function (i) {
		if (i === 0) return this.boundable1;
		return this.boundable2;
	},
	getDistance: function () {
		return this._distance;
	},
	distance: function () {
		if (this.isLeaves()) {
			return this.itemDistance.distance(this.boundable1, this.boundable2);
		}
		return this.boundable1.getBounds().distance(this.boundable2.getBounds());
	},
	interfaces_: function () {
		return [Comparable];
	},
	getClass: function () {
		return BoundablePair;
	}
});
BoundablePair.area = function (b) {
	return b.getBounds().getArea();
};
BoundablePair.isComposite = function (item) {
	return item instanceof AbstractNode;
};

function AbstractSTRtree() {
	this.root = null;
	this.built = false;
	this.itemBoundables = new ArrayList();
	this.nodeCapacity = null;
	if (arguments.length === 0) {
		AbstractSTRtree.call(this, AbstractSTRtree.DEFAULT_NODE_CAPACITY);
	} else if (arguments.length === 1) {
		let nodeCapacity = arguments[0];
		Assert.isTrue(nodeCapacity > 1, "Node capacity must be greater than 1");
		this.nodeCapacity = nodeCapacity;
	}
}
extend$1(AbstractSTRtree.prototype, {
	getNodeCapacity: function () {
		return this.nodeCapacity;
	},
	lastNode: function (nodes) {
		return nodes.get(nodes.size() - 1);
	},
	size: function () {
		if (arguments.length === 0) {
			if (this.isEmpty()) {
				return 0;
			}
			this.build();
			return this.size(this.root);
		} else if (arguments.length === 1) {
			let node = arguments[0];
			var size = 0;
			for (var i = node.getChildBoundables().iterator(); i.hasNext(); ) {
				var childBoundable = i.next();
				if (childBoundable instanceof AbstractNode) {
					size += this.size(childBoundable);
				} else if (childBoundable instanceof ItemBoundable) {
					size += 1;
				}
			}
			return size;
		}
	},
	removeItem: function (node, item) {
		var childToRemove = null;
		for (var i = node.getChildBoundables().iterator(); i.hasNext(); ) {
			var childBoundable = i.next();
			if (childBoundable instanceof ItemBoundable) {
				if (childBoundable.getItem() === item) childToRemove = childBoundable;
			}
		}
		if (childToRemove !== null) {
			node.getChildBoundables().remove(childToRemove);
			return true;
		}
		return false;
	},
	itemsTree: function () {
		if (arguments.length === 0) {
			this.build();
			var valuesTree = this.itemsTree(this.root);
			if (valuesTree === null) return new ArrayList();
			return valuesTree;
		} else if (arguments.length === 1) {
			let node = arguments[0];
			var valuesTreeForNode = new ArrayList();
			for (var i = node.getChildBoundables().iterator(); i.hasNext(); ) {
				var childBoundable = i.next();
				if (childBoundable instanceof AbstractNode) {
					var valuesTreeForChild = this.itemsTree(childBoundable);
					if (valuesTreeForChild !== null) valuesTreeForNode.add(valuesTreeForChild);
				} else if (childBoundable instanceof ItemBoundable) {
					valuesTreeForNode.add(childBoundable.getItem());
				} else {
					Assert.shouldNeverReachHere();
				}
			}
			if (valuesTreeForNode.size() <= 0) return null;
			return valuesTreeForNode;
		}
	},
	insert: function (bounds, item) {
		Assert.isTrue(!this.built, "Cannot insert items into an STR packed R-tree after it has been built.");
		this.itemBoundables.add(new ItemBoundable(bounds, item));
	},
	boundablesAtLevel: function () {
		if (arguments.length === 1) {
			let level = arguments[0];
			var boundables = new ArrayList();
			this.boundablesAtLevel(level, this.root, boundables);
			return boundables;
		} else if (arguments.length === 3) {
			let level = arguments[0], top = arguments[1], boundables = arguments[2];
			Assert.isTrue(level > -2);
			if (top.getLevel() === level) {
				boundables.add(top);
				return null;
			}
			for (var i = top.getChildBoundables().iterator(); i.hasNext(); ) {
				var boundable = i.next();
				if (boundable instanceof AbstractNode) {
					this.boundablesAtLevel(level, boundable, boundables);
				} else {
					Assert.isTrue(boundable instanceof ItemBoundable);
					if (level === -1) {
						boundables.add(boundable);
					}
				}
			}
			return null;
		}
	},
	query: function () {
		if (arguments.length === 1) {
			let searchBounds = arguments[0];
			this.build();
			var matches = new ArrayList();
			if (this.isEmpty()) {
				return matches;
			}
			if (this.getIntersectsOp().intersects(this.root.getBounds(), searchBounds)) {
				this.query(searchBounds, this.root, matches);
			}
			return matches;
		} else if (arguments.length === 2) {
			let searchBounds = arguments[0], visitor = arguments[1];
			this.build();
			if (this.isEmpty()) {
				return null;
			}
			if (this.getIntersectsOp().intersects(this.root.getBounds(), searchBounds)) {
				this.query(searchBounds, this.root, visitor);
			}
		} else if (arguments.length === 3) {
			if (hasInterface(arguments[2], ItemVisitor) && (arguments[0] instanceof Object && arguments[1] instanceof AbstractNode)) {
				let searchBounds = arguments[0], node = arguments[1], visitor = arguments[2];
				var childBoundables = node.getChildBoundables();
				for (var i = 0; i < childBoundables.size(); i++) {
					var childBoundable = childBoundables.get(i);
					if (!this.getIntersectsOp().intersects(childBoundable.getBounds(), searchBounds)) {
						continue;
					}
					if (childBoundable instanceof AbstractNode) {
						this.query(searchBounds, childBoundable, visitor);
					} else if (childBoundable instanceof ItemBoundable) {
						visitor.visitItem(childBoundable.getItem());
					} else {
						Assert.shouldNeverReachHere();
					}
				}
			} else if (hasInterface(arguments[2], List) && (arguments[0] instanceof Object && arguments[1] instanceof AbstractNode)) {
				let searchBounds = arguments[0], node = arguments[1], matches = arguments[2];
				var childBoundables = node.getChildBoundables();
				for (var i = 0; i < childBoundables.size(); i++) {
					var childBoundable = childBoundables.get(i);
					if (!this.getIntersectsOp().intersects(childBoundable.getBounds(), searchBounds)) {
						continue;
					}
					if (childBoundable instanceof AbstractNode) {
						this.query(searchBounds, childBoundable, matches);
					} else if (childBoundable instanceof ItemBoundable) {
						matches.add(childBoundable.getItem());
					} else {
						Assert.shouldNeverReachHere();
					}
				}
			}
		}
	},
	build: function () {
		if (this.built) return null;
		this.root = this.itemBoundables.isEmpty() ? this.createNode(0) : this.createHigherLevels(this.itemBoundables, -1);
		this.itemBoundables = null;
		this.built = true;
	},
	getRoot: function () {
		this.build();
		return this.root;
	},
	remove: function () {
		if (arguments.length === 2) {
			let searchBounds = arguments[0], item = arguments[1];
			this.build();
			if (this.getIntersectsOp().intersects(this.root.getBounds(), searchBounds)) {
				return this.remove(searchBounds, this.root, item);
			}
			return false;
		} else if (arguments.length === 3) {
			let searchBounds = arguments[0], node = arguments[1], item = arguments[2];
			var found = this.removeItem(node, item);
			if (found) return true;
			var childToPrune = null;
			for (var i = node.getChildBoundables().iterator(); i.hasNext(); ) {
				var childBoundable = i.next();
				if (!this.getIntersectsOp().intersects(childBoundable.getBounds(), searchBounds)) {
					continue;
				}
				if (childBoundable instanceof AbstractNode) {
					found = this.remove(searchBounds, childBoundable, item);
					if (found) {
						childToPrune = childBoundable;
						break;
					}
				}
			}
			if (childToPrune !== null) {
				if (childToPrune.getChildBoundables().isEmpty()) {
					node.getChildBoundables().remove(childToPrune);
				}
			}
			return found;
		}
	},
	createHigherLevels: function (boundablesOfALevel, level) {
		Assert.isTrue(!boundablesOfALevel.isEmpty());
		var parentBoundables = this.createParentBoundables(boundablesOfALevel, level + 1);
		if (parentBoundables.size() === 1) {
			return parentBoundables.get(0);
		}
		return this.createHigherLevels(parentBoundables, level + 1);
	},
	depth: function () {
		if (arguments.length === 0) {
			if (this.isEmpty()) {
				return 0;
			}
			this.build();
			return this.depth(this.root);
		} else if (arguments.length === 1) {
			let node = arguments[0];
			var maxChildDepth = 0;
			for (var i = node.getChildBoundables().iterator(); i.hasNext(); ) {
				var childBoundable = i.next();
				if (childBoundable instanceof AbstractNode) {
					var childDepth = this.depth(childBoundable);
					if (childDepth > maxChildDepth) maxChildDepth = childDepth;
				}
			}
			return maxChildDepth + 1;
		}
	},
	createParentBoundables: function (childBoundables, newLevel) {
		Assert.isTrue(!childBoundables.isEmpty());
		var parentBoundables = new ArrayList();
		parentBoundables.add(this.createNode(newLevel));
		var sortedChildBoundables = new ArrayList(childBoundables);
		Collections.sort(sortedChildBoundables, this.getComparator());
		for (var i = sortedChildBoundables.iterator(); i.hasNext(); ) {
			var childBoundable = i.next();
			if (this.lastNode(parentBoundables).getChildBoundables().size() === this.getNodeCapacity()) {
				parentBoundables.add(this.createNode(newLevel));
			}
			this.lastNode(parentBoundables).addChildBoundable(childBoundable);
		}
		return parentBoundables;
	},
	isEmpty: function () {
		if (!this.built) return this.itemBoundables.isEmpty();
		return this.root.isEmpty();
	},
	interfaces_: function () {
		return [Serializable];
	},
	getClass: function () {
		return AbstractSTRtree;
	}
});
AbstractSTRtree.compareDoubles = function (a, b) {
	return a > b ? 1 : a < b ? -1 : 0;
};
function IntersectsOp$1() {}
AbstractSTRtree.IntersectsOp = IntersectsOp$1;
AbstractSTRtree.serialVersionUID = -3886435814360241337;
AbstractSTRtree.DEFAULT_NODE_CAPACITY = 10;

function ItemDistance() {}
extend$1(ItemDistance.prototype, {
	distance: function (item1, item2) {},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return ItemDistance;
	}
});

function STRtree() {
	if (arguments.length === 0) {
		STRtree.call(this, STRtree.DEFAULT_NODE_CAPACITY);
	} else if (arguments.length === 1) {
		let nodeCapacity = arguments[0];
		AbstractSTRtree.call(this, nodeCapacity);
	}
}
inherits(STRtree, AbstractSTRtree);
extend$1(STRtree.prototype, {
	createParentBoundablesFromVerticalSlices: function (verticalSlices, newLevel) {
		Assert.isTrue(verticalSlices.length > 0);
		var parentBoundables = new ArrayList();
		for (var i = 0; i < verticalSlices.length; i++) {
			parentBoundables.addAll(this.createParentBoundablesFromVerticalSlice(verticalSlices[i], newLevel));
		}
		return parentBoundables;
	},
	createNode: function (level) {
		return new STRtreeNode(level);
	},
	size: function () {
		if (arguments.length === 0) {
			return AbstractSTRtree.prototype.size.call(this);
		} else return AbstractSTRtree.prototype.size.apply(this, arguments);
	},
	insert: function () {
		if (arguments.length === 2) {
			let itemEnv = arguments[0], item = arguments[1];
			if (itemEnv.isNull()) {
				return null;
			}
			AbstractSTRtree.prototype.insert.call(this, itemEnv, item);
		} else return AbstractSTRtree.prototype.insert.apply(this, arguments);
	},
	getIntersectsOp: function () {
		return STRtree.intersectsOp;
	},
	verticalSlices: function (childBoundables, sliceCount) {
		var sliceCapacity = Math.trunc(Math.ceil(childBoundables.size() / sliceCount));
		var slices = new Array(sliceCount).fill(null);
		var i = childBoundables.iterator();
		for (var j = 0; j < sliceCount; j++) {
			slices[j] = new ArrayList();
			var boundablesAddedToSlice = 0;
			while (i.hasNext() && boundablesAddedToSlice < sliceCapacity) {
				var childBoundable = i.next();
				slices[j].add(childBoundable);
				boundablesAddedToSlice++;
			}
		}
		return slices;
	},
	query: function () {
		if (arguments.length === 1) {
			let searchEnv = arguments[0];
			return AbstractSTRtree.prototype.query.call(this, searchEnv);
		} else if (arguments.length === 2) {
			let searchEnv = arguments[0], visitor = arguments[1];
			AbstractSTRtree.prototype.query.call(this, searchEnv, visitor);
		} else if (arguments.length === 3) {
			if (hasInterface(arguments[2], ItemVisitor) && (arguments[0] instanceof Object && arguments[1] instanceof AbstractNode)) {
				let searchBounds = arguments[0], node = arguments[1], visitor = arguments[2];
				AbstractSTRtree.prototype.query.call(this, searchBounds, node, visitor);
			} else if (hasInterface(arguments[2], List) && (arguments[0] instanceof Object && arguments[1] instanceof AbstractNode)) {
				let searchBounds = arguments[0], node = arguments[1], matches = arguments[2];
				AbstractSTRtree.prototype.query.call(this, searchBounds, node, matches);
			}
		}
	},
	getComparator: function () {
		return STRtree.yComparator;
	},
	createParentBoundablesFromVerticalSlice: function (childBoundables, newLevel) {
		return AbstractSTRtree.prototype.createParentBoundables.call(this, childBoundables, newLevel);
	},
	remove: function () {
		if (arguments.length === 2) {
			let itemEnv = arguments[0], item = arguments[1];
			return AbstractSTRtree.prototype.remove.call(this, itemEnv, item);
		} else return AbstractSTRtree.prototype.remove.apply(this, arguments);
	},
	depth: function () {
		if (arguments.length === 0) {
			return AbstractSTRtree.prototype.depth.call(this);
		} else return AbstractSTRtree.prototype.depth.apply(this, arguments);
	},
	createParentBoundables: function (childBoundables, newLevel) {
		Assert.isTrue(!childBoundables.isEmpty());
		var minLeafCount = Math.trunc(Math.ceil(childBoundables.size() / this.getNodeCapacity()));
		var sortedChildBoundables = new ArrayList(childBoundables);
		Collections.sort(sortedChildBoundables, STRtree.xComparator);
		var verticalSlices = this.verticalSlices(sortedChildBoundables, Math.trunc(Math.ceil(Math.sqrt(minLeafCount))));
		return this.createParentBoundablesFromVerticalSlices(verticalSlices, newLevel);
	},
	nearestNeighbour: function () {
		if (arguments.length === 1) {
			if (hasInterface(arguments[0], ItemDistance)) {
				let itemDist = arguments[0];
				var bp = new BoundablePair(this.getRoot(), this.getRoot(), itemDist);
				return this.nearestNeighbour(bp);
			} else if (arguments[0] instanceof BoundablePair) {
				let initBndPair = arguments[0];
				return this.nearestNeighbour(initBndPair, Double.POSITIVE_INFINITY);
			}
		} else if (arguments.length === 2) {
			if (arguments[0] instanceof STRtree && hasInterface(arguments[1], ItemDistance)) {
				let tree = arguments[0], itemDist = arguments[1];
				var bp = new BoundablePair(this.getRoot(), tree.getRoot(), itemDist);
				return this.nearestNeighbour(bp);
			} else if (arguments[0] instanceof BoundablePair && typeof arguments[1] === "number") {
				let initBndPair = arguments[0], maxDistance = arguments[1];
				var distanceLowerBound = maxDistance;
				var minPair = null;
				var priQ = new PriorityQueue();
				priQ.add(initBndPair);
				while (!priQ.isEmpty() && distanceLowerBound > 0.0) {
					var bndPair = priQ.poll();
					var currentDistance = bndPair.getDistance();
					if (currentDistance >= distanceLowerBound) break;
					if (bndPair.isLeaves()) {
						distanceLowerBound = currentDistance;
						minPair = bndPair;
					} else {
						bndPair.expandToQueue(priQ, distanceLowerBound);
					}
				}
				return [minPair.getBoundable(0).getItem(), minPair.getBoundable(1).getItem()];
			}
		} else if (arguments.length === 3) {
			let env = arguments[0], item = arguments[1], itemDist = arguments[2];
			var bnd = new ItemBoundable(env, item);
			var bp = new BoundablePair(this.getRoot(), bnd, itemDist);
			return this.nearestNeighbour(bp)[0];
		}
	},
	interfaces_: function () {
		return [SpatialIndex, Serializable];
	},
	getClass: function () {
		return STRtree;
	}
});
STRtree.centreX = function (e) {
	return STRtree.avg(e.getMinX(), e.getMaxX());
};
STRtree.avg = function (a, b) {
	return (a + b) / 2;
};
STRtree.centreY = function (e) {
	return STRtree.avg(e.getMinY(), e.getMaxY());
};
function STRtreeNode() {
	let level = arguments[0];
	AbstractNode.call(this, level);
}
inherits(STRtreeNode, AbstractNode);
extend$1(STRtreeNode.prototype, {
	computeBounds: function () {
		var bounds = null;
		for (var i = this.getChildBoundables().iterator(); i.hasNext(); ) {
			var childBoundable = i.next();
			if (bounds === null) {
				bounds = new Envelope(childBoundable.getBounds());
			} else {
				bounds.expandToInclude(childBoundable.getBounds());
			}
		}
		return bounds;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return STRtreeNode;
	}
});
STRtree.STRtreeNode = STRtreeNode;
STRtree.serialVersionUID = 259274702368956900;
STRtree.xComparator = {
	interfaces_: function () {
		return [Comparator];
	},
	compare: function (o1, o2) {
		return AbstractSTRtree.compareDoubles(STRtree.centreX(o1.getBounds()), STRtree.centreX(o2.getBounds()));
	}
};
STRtree.yComparator = {
	interfaces_: function () {
		return [Comparator];
	},
	compare: function (o1, o2) {
		return AbstractSTRtree.compareDoubles(STRtree.centreY(o1.getBounds()), STRtree.centreY(o2.getBounds()));
	}
};
STRtree.intersectsOp = {
	interfaces_: function () {
		return [IntersectsOp];
	},
	intersects: function (aBounds, bBounds) {
		return aBounds.intersects(bBounds);
	}
};
STRtree.DEFAULT_NODE_CAPACITY = 10;

function IndexedNestedRingTester() {
	this.graph = null;
	this.rings = new ArrayList();
	this.totalEnv = new Envelope();
	this.index = null;
	this.nestedPt = null;
	let graph = arguments[0];
	this.graph = graph;
}
extend$1(IndexedNestedRingTester.prototype, {
	buildIndex: function () {
		this.index = new STRtree();
		for (var i = 0; i < this.rings.size(); i++) {
			var ring = this.rings.get(i);
			var env = ring.getEnvelopeInternal();
			this.index.insert(env, ring);
		}
	},
	getNestedPoint: function () {
		return this.nestedPt;
	},
	isNonNested: function () {
		this.buildIndex();
		for (var i = 0; i < this.rings.size(); i++) {
			var innerRing = this.rings.get(i);
			var innerRingPts = innerRing.getCoordinates();
			var results = this.index.query(innerRing.getEnvelopeInternal());
			for (var j = 0; j < results.size(); j++) {
				var searchRing = results.get(j);
				var searchRingPts = searchRing.getCoordinates();
				if (innerRing === searchRing) continue;
				if (!innerRing.getEnvelopeInternal().intersects(searchRing.getEnvelopeInternal())) continue;
				var innerRingPt = IsValidOp.findPtNotNode(innerRingPts, searchRing, this.graph);
				if (innerRingPt === null) continue;
				var isInside = CGAlgorithms.isPointInRing(innerRingPt, searchRingPts);
				if (isInside) {
					this.nestedPt = innerRingPt;
					return false;
				}
			}
		}
		return true;
	},
	add: function (ring) {
		this.rings.add(ring);
		this.totalEnv.expandToInclude(ring.getEnvelopeInternal());
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return IndexedNestedRingTester;
	}
});

function TopologyValidationError() {
	this.errorType = null;
	this.pt = null;
	if (arguments.length === 1) {
		let errorType = arguments[0];
		TopologyValidationError.call(this, errorType, null);
	} else if (arguments.length === 2) {
		let errorType = arguments[0], pt = arguments[1];
		this.errorType = errorType;
		if (pt !== null) this.pt = pt.copy();
	}
}
extend$1(TopologyValidationError.prototype, {
	getErrorType: function () {
		return this.errorType;
	},
	getMessage: function () {
		return TopologyValidationError.errMsg[this.errorType];
	},
	getCoordinate: function () {
		return this.pt;
	},
	toString: function () {
		var locStr = "";
		if (this.pt !== null) locStr = " at or near point " + this.pt;
		return this.getMessage() + locStr;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return TopologyValidationError;
	}
});
TopologyValidationError.ERROR = 0;
TopologyValidationError.REPEATED_POINT = 1;
TopologyValidationError.HOLE_OUTSIDE_SHELL = 2;
TopologyValidationError.NESTED_HOLES = 3;
TopologyValidationError.DISCONNECTED_INTERIOR = 4;
TopologyValidationError.SELF_INTERSECTION = 5;
TopologyValidationError.RING_SELF_INTERSECTION = 6;
TopologyValidationError.NESTED_SHELLS = 7;
TopologyValidationError.DUPLICATE_RINGS = 8;
TopologyValidationError.TOO_FEW_POINTS = 9;
TopologyValidationError.INVALID_COORDINATE = 10;
TopologyValidationError.RING_NOT_CLOSED = 11;
TopologyValidationError.errMsg = ["Topology Validation Error", "Repeated Point", "Hole lies outside shell", "Holes are nested", "Interior is disconnected", "Self-intersection", "Ring Self-intersection", "Nested shells", "Duplicate Rings", "Too few distinct points in geometry component", "Invalid Coordinate", "Ring is not closed"];

function IsValidOp() {
	this.parentGeometry = null;
	this.isSelfTouchingRingFormingHoleValid = false;
	this.validErr = null;
	let parentGeometry = arguments[0];
	this.parentGeometry = parentGeometry;
}
extend$1(IsValidOp.prototype, {
	checkInvalidCoordinates: function () {
		if (arguments[0] instanceof Array) {
			let coords = arguments[0];
			for (var i = 0; i < coords.length; i++) {
				if (!IsValidOp.isValid(coords[i])) {
					this.validErr = new TopologyValidationError(TopologyValidationError.INVALID_COORDINATE, coords[i]);
					return null;
				}
			}
		} else if (arguments[0] instanceof Polygon) {
			let poly = arguments[0];
			this.checkInvalidCoordinates(poly.getExteriorRing().getCoordinates());
			if (this.validErr !== null) return null;
			for (var i = 0; i < poly.getNumInteriorRing(); i++) {
				this.checkInvalidCoordinates(poly.getInteriorRingN(i).getCoordinates());
				if (this.validErr !== null) return null;
			}
		}
	},
	checkHolesNotNested: function (p, graph) {
		var nestedTester = new IndexedNestedRingTester(graph);
		for (var i = 0; i < p.getNumInteriorRing(); i++) {
			var innerHole = p.getInteriorRingN(i);
			nestedTester.add(innerHole);
		}
		var isNonNested = nestedTester.isNonNested();
		if (!isNonNested) {
			this.validErr = new TopologyValidationError(TopologyValidationError.NESTED_HOLES, nestedTester.getNestedPoint());
		}
	},
	checkConsistentArea: function (graph) {
		var cat = new ConsistentAreaTester(graph);
		var isValidArea = cat.isNodeConsistentArea();
		if (!isValidArea) {
			this.validErr = new TopologyValidationError(TopologyValidationError.SELF_INTERSECTION, cat.getInvalidPoint());
			return null;
		}
		if (cat.hasDuplicateRings()) {
			this.validErr = new TopologyValidationError(TopologyValidationError.DUPLICATE_RINGS, cat.getInvalidPoint());
		}
	},
	isValid: function () {
		this.checkValid(this.parentGeometry);
		return this.validErr === null;
	},
	checkShellInsideHole: function (shell, hole, graph) {
		var shellPts = shell.getCoordinates();
		var holePts = hole.getCoordinates();
		var shellPt = IsValidOp.findPtNotNode(shellPts, hole, graph);
		if (shellPt !== null) {
			var insideHole = CGAlgorithms.isPointInRing(shellPt, holePts);
			if (!insideHole) {
				return shellPt;
			}
		}
		var holePt = IsValidOp.findPtNotNode(holePts, shell, graph);
		if (holePt !== null) {
			var insideShell = CGAlgorithms.isPointInRing(holePt, shellPts);
			if (insideShell) {
				return holePt;
			}
			return null;
		}
		Assert.shouldNeverReachHere("points in shell and hole appear to be equal");
		return null;
	},
	checkNoSelfIntersectingRings: function (graph) {
		for (var i = graph.getEdgeIterator(); i.hasNext(); ) {
			var e = i.next();
			this.checkNoSelfIntersectingRing(e.getEdgeIntersectionList());
			if (this.validErr !== null) return null;
		}
	},
	checkConnectedInteriors: function (graph) {
		var cit = new ConnectedInteriorTester(graph);
		if (!cit.isInteriorsConnected()) this.validErr = new TopologyValidationError(TopologyValidationError.DISCONNECTED_INTERIOR, cit.getCoordinate());
	},
	checkNoSelfIntersectingRing: function (eiList) {
		var nodeSet = new TreeSet();
		var isFirst = true;
		for (var i = eiList.iterator(); i.hasNext(); ) {
			var ei = i.next();
			if (isFirst) {
				isFirst = false;
				continue;
			}
			if (nodeSet.contains(ei.coord)) {
				this.validErr = new TopologyValidationError(TopologyValidationError.RING_SELF_INTERSECTION, ei.coord);
				return null;
			} else {
				nodeSet.add(ei.coord);
			}
		}
	},
	checkHolesInShell: function (p, graph) {
		var shell = p.getExteriorRing();
		var pir = new MCPointInRing(shell);
		for (var i = 0; i < p.getNumInteriorRing(); i++) {
			var hole = p.getInteriorRingN(i);
			var holePt = IsValidOp.findPtNotNode(hole.getCoordinates(), shell, graph);
			if (holePt === null) return null;
			var outside = !pir.isInside(holePt);
			if (outside) {
				this.validErr = new TopologyValidationError(TopologyValidationError.HOLE_OUTSIDE_SHELL, holePt);
				return null;
			}
		}
	},
	checkTooFewPoints: function (graph) {
		if (graph.hasTooFewPoints()) {
			this.validErr = new TopologyValidationError(TopologyValidationError.TOO_FEW_POINTS, graph.getInvalidPoint());
			return null;
		}
	},
	getValidationError: function () {
		this.checkValid(this.parentGeometry);
		return this.validErr;
	},
	checkValid: function () {
		if (arguments[0] instanceof Point) {
			let g = arguments[0];
			this.checkInvalidCoordinates(g.getCoordinates());
		} else if (arguments[0] instanceof MultiPoint) {
			let g = arguments[0];
			this.checkInvalidCoordinates(g.getCoordinates());
		} else if (arguments[0] instanceof LinearRing) {
			let g = arguments[0];
			this.checkInvalidCoordinates(g.getCoordinates());
			if (this.validErr !== null) return null;
			this.checkClosedRing(g);
			if (this.validErr !== null) return null;
			var graph = new GeometryGraph(0, g);
			this.checkTooFewPoints(graph);
			if (this.validErr !== null) return null;
			var li = new RobustLineIntersector();
			graph.computeSelfNodes(li, true, true);
			this.checkNoSelfIntersectingRings(graph);
		} else if (arguments[0] instanceof LineString) {
			let g = arguments[0];
			this.checkInvalidCoordinates(g.getCoordinates());
			if (this.validErr !== null) return null;
			var graph = new GeometryGraph(0, g);
			this.checkTooFewPoints(graph);
		} else if (arguments[0] instanceof Polygon) {
			let g = arguments[0];
			this.checkInvalidCoordinates(g);
			if (this.validErr !== null) return null;
			this.checkClosedRings(g);
			if (this.validErr !== null) return null;
			var graph = new GeometryGraph(0, g);
			this.checkTooFewPoints(graph);
			if (this.validErr !== null) return null;
			this.checkConsistentArea(graph);
			if (this.validErr !== null) return null;
			if (!this.isSelfTouchingRingFormingHoleValid) {
				this.checkNoSelfIntersectingRings(graph);
				if (this.validErr !== null) return null;
			}
			this.checkHolesInShell(g, graph);
			if (this.validErr !== null) return null;
			this.checkHolesNotNested(g, graph);
			if (this.validErr !== null) return null;
			this.checkConnectedInteriors(graph);
		} else if (arguments[0] instanceof MultiPolygon) {
			let g = arguments[0];
			for (var i = 0; i < g.getNumGeometries(); i++) {
				var p = g.getGeometryN(i);
				this.checkInvalidCoordinates(p);
				if (this.validErr !== null) return null;
				this.checkClosedRings(p);
				if (this.validErr !== null) return null;
			}
			var graph = new GeometryGraph(0, g);
			this.checkTooFewPoints(graph);
			if (this.validErr !== null) return null;
			this.checkConsistentArea(graph);
			if (this.validErr !== null) return null;
			if (!this.isSelfTouchingRingFormingHoleValid) {
				this.checkNoSelfIntersectingRings(graph);
				if (this.validErr !== null) return null;
			}
			for (var i = 0; i < g.getNumGeometries(); i++) {
				var p = g.getGeometryN(i);
				this.checkHolesInShell(p, graph);
				if (this.validErr !== null) return null;
			}
			for (var i = 0; i < g.getNumGeometries(); i++) {
				var p = g.getGeometryN(i);
				this.checkHolesNotNested(p, graph);
				if (this.validErr !== null) return null;
			}
			this.checkShellsNotNested(g, graph);
			if (this.validErr !== null) return null;
			this.checkConnectedInteriors(graph);
		} else if (arguments[0] instanceof GeometryCollection) {
			let gc = arguments[0];
			for (var i = 0; i < gc.getNumGeometries(); i++) {
				var g = gc.getGeometryN(i);
				this.checkValid(g);
				if (this.validErr !== null) return null;
			}
		} else if (arguments[0] instanceof Geometry) {
			let g = arguments[0];
			this.validErr = null;
			if (g.isEmpty()) return null;
			if (g instanceof Point) this.checkValid(g); else if (g instanceof MultiPoint) this.checkValid(g); else if (g instanceof LinearRing) this.checkValid(g); else if (g instanceof LineString) this.checkValid(g); else if (g instanceof Polygon) this.checkValid(g); else if (g instanceof MultiPolygon) this.checkValid(g); else if (g instanceof GeometryCollection) this.checkValid(g); else throw new UnsupportedOperationException(g.getClass().getName());
		}
	},
	setSelfTouchingRingFormingHoleValid: function (isValid) {
		this.isSelfTouchingRingFormingHoleValid = isValid;
	},
	checkShellNotNested: function (shell, p, graph) {
		var shellPts = shell.getCoordinates();
		var polyShell = p.getExteriorRing();
		var polyPts = polyShell.getCoordinates();
		var shellPt = IsValidOp.findPtNotNode(shellPts, polyShell, graph);
		if (shellPt === null) return null;
		var insidePolyShell = CGAlgorithms.isPointInRing(shellPt, polyPts);
		if (!insidePolyShell) return null;
		if (p.getNumInteriorRing() <= 0) {
			this.validErr = new TopologyValidationError(TopologyValidationError.NESTED_SHELLS, shellPt);
			return null;
		}
		var badNestedPt = null;
		for (var i = 0; i < p.getNumInteriorRing(); i++) {
			var hole = p.getInteriorRingN(i);
			badNestedPt = this.checkShellInsideHole(shell, hole, graph);
			if (badNestedPt === null) return null;
		}
		this.validErr = new TopologyValidationError(TopologyValidationError.NESTED_SHELLS, badNestedPt);
	},
	checkClosedRings: function (poly) {
		this.checkClosedRing(poly.getExteriorRing());
		if (this.validErr !== null) return null;
		for (var i = 0; i < poly.getNumInteriorRing(); i++) {
			this.checkClosedRing(poly.getInteriorRingN(i));
			if (this.validErr !== null) return null;
		}
	},
	checkClosedRing: function (ring) {
		if (!ring.isClosed()) {
			var pt = null;
			if (ring.getNumPoints() >= 1) pt = ring.getCoordinateN(0);
			this.validErr = new TopologyValidationError(TopologyValidationError.RING_NOT_CLOSED, pt);
		}
	},
	checkShellsNotNested: function (mp, graph) {
		for (var i = 0; i < mp.getNumGeometries(); i++) {
			var p = mp.getGeometryN(i);
			var shell = p.getExteriorRing();
			for (var j = 0; j < mp.getNumGeometries(); j++) {
				if (i === j) continue;
				var p2 = mp.getGeometryN(j);
				this.checkShellNotNested(shell, p2, graph);
				if (this.validErr !== null) return null;
			}
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return IsValidOp;
	}
});
IsValidOp.findPtNotNode = function (testCoords, searchRing, graph) {
	var searchEdge = graph.findEdge(searchRing);
	var eiList = searchEdge.getEdgeIntersectionList();
	for (var i = 0; i < testCoords.length; i++) {
		var pt = testCoords[i];
		if (!eiList.isIntersection(pt)) return pt;
	}
	return null;
};
IsValidOp.isValid = function () {
	if (arguments[0] instanceof Geometry) {
		let geom = arguments[0];
		var isValidOp = new IsValidOp(geom);
		return isValidOp.isValid();
	} else if (arguments[0] instanceof Coordinate) {
		let coord = arguments[0];
		if (Double.isNaN(coord.x)) return false;
		if (Double.isInfinite(coord.x)) return false;
		if (Double.isNaN(coord.y)) return false;
		if (Double.isInfinite(coord.y)) return false;
		return true;
	}
};

function EdgeRing() {
	this.factory = null;
	this.deList = new ArrayList();
	this.lowestEdge = null;
	this.ring = null;
	this.ringPts = null;
	this.holes = null;
	this.shell = null;
	this._isHole = null;
	this._isProcessed = false;
	this._isIncludedSet = false;
	this._isIncluded = false;
	let factory = arguments[0];
	this.factory = factory;
}
extend$1(EdgeRing.prototype, {
	isIncluded: function () {
		return this._isIncluded;
	},
	getCoordinates: function () {
		if (this.ringPts === null) {
			var coordList = new CoordinateList();
			for (var i = this.deList.iterator(); i.hasNext(); ) {
				var de = i.next();
				var edge = de.getEdge();
				EdgeRing.addEdge(edge.getLine().getCoordinates(), de.getEdgeDirection(), coordList);
			}
			this.ringPts = coordList.toCoordinateArray();
		}
		return this.ringPts;
	},
	isIncludedSet: function () {
		return this._isIncludedSet;
	},
	isValid: function () {
		this.getCoordinates();
		if (this.ringPts.length <= 3) return false;
		this.getRing();
		return IsValidOp.isValid(this.ring);
	},
	build: function (startDE) {
		var de = startDE;
		do {
			this.add(de);
			de.setRing(this);
			de = de.getNext();
			Assert.isTrue(de !== null, "found null DE in ring");
			Assert.isTrue(de === startDE || !de.isInRing(), "found DE already in ring");
		} while (de !== startDE);
	},
	isOuterHole: function () {
		if (!this._isHole) return false;
		return !this.hasShell();
	},
	getPolygon: function () {
		var holeLR = null;
		if (this.holes !== null) {
			holeLR = new Array(this.holes.size()).fill(null);
			for (var i = 0; i < this.holes.size(); i++) {
				holeLR[i] = this.holes.get(i);
			}
		}
		var poly = this.factory.createPolygon(this.ring, holeLR);
		return poly;
	},
	isHole: function () {
		return this._isHole;
	},
	isProcessed: function () {
		return this._isProcessed;
	},
	addHole: function () {
		if (arguments[0] instanceof LinearRing) {
			let hole = arguments[0];
			if (this.holes === null) this.holes = new ArrayList();
			this.holes.add(hole);
		} else if (arguments[0] instanceof EdgeRing) {
			let holeER = arguments[0];
			holeER.setShell(this);
			var hole = holeER.getRing();
			if (this.holes === null) this.holes = new ArrayList();
			this.holes.add(hole);
		}
	},
	setIncluded: function (isIncluded) {
		this._isIncluded = isIncluded;
		this._isIncludedSet = true;
	},
	getOuterHole: function () {
		if (this.isHole()) return null;
		for (var i = 0; i < this.deList.size(); i++) {
			var de = this.deList.get(i);
			var adjRing = de.getSym().getRing();
			if (adjRing.isOuterHole()) return adjRing;
		}
		return null;
	},
	computeHole: function () {
		var ring = this.getRing();
		this._isHole = CGAlgorithms.isCCW(ring.getCoordinates());
	},
	hasShell: function () {
		return this.shell !== null;
	},
	isOuterShell: function () {
		return this.getOuterHole() !== null;
	},
	getLineString: function () {
		this.getCoordinates();
		return this.factory.createLineString(this.ringPts);
	},
	toString: function () {
		return WKTWriter.toLineString(new CoordinateArraySequence(this.getCoordinates()));
	},
	getShell: function () {
		if (this.isHole()) return this.shell;
		return this;
	},
	add: function (de) {
		this.deList.add(de);
	},
	getRing: function () {
		if (this.ring !== null) return this.ring;
		this.getCoordinates();
		if (this.ringPts.length < 3) System.out.println(this.ringPts);
		try {
			this.ring = this.factory.createLinearRing(this.ringPts);
		} catch (ex) {
			if (ex instanceof Exception) {
				System.out.println(this.ringPts);
			} else throw ex;
		} finally {}
		return this.ring;
	},
	updateIncluded: function () {
		if (this.isHole()) return null;
		for (var i = 0; i < this.deList.size(); i++) {
			var de = this.deList.get(i);
			var adjShell = de.getSym().getRing().getShell();
			if (adjShell !== null && adjShell.isIncludedSet()) {
				this.setIncluded(!adjShell.isIncluded());
				return null;
			}
		}
	},
	setShell: function (shell) {
		this.shell = shell;
	},
	setProcessed: function (isProcessed) {
		this._isProcessed = isProcessed;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return EdgeRing;
	}
});
EdgeRing.findDirEdgesInRing = function (startDE) {
	var de = startDE;
	var edges = new ArrayList();
	do {
		edges.add(de);
		de = de.getNext();
		Assert.isTrue(de !== null, "found null DE in ring");
		Assert.isTrue(de === startDE || !de.isInRing(), "found DE already in ring");
	} while (de !== startDE);
	return edges;
};
EdgeRing.addEdge = function (coords, isForward, coordList) {
	if (isForward) {
		for (var i = 0; i < coords.length; i++) {
			coordList.add(coords[i], false);
		}
	} else {
		for (var i = coords.length - 1; i >= 0; i--) {
			coordList.add(coords[i], false);
		}
	}
};
EdgeRing.findEdgeRingContaining = function (testEr, shellList) {
	var testRing = testEr.getRing();
	var testEnv = testRing.getEnvelopeInternal();
	var testPt = testRing.getCoordinateN(0);
	var minShell = null;
	var minShellEnv = null;
	for (var it = shellList.iterator(); it.hasNext(); ) {
		var tryShell = it.next();
		var tryShellRing = tryShell.getRing();
		var tryShellEnv = tryShellRing.getEnvelopeInternal();
		if (tryShellEnv.equals(testEnv)) continue;
		if (!tryShellEnv.contains(testEnv)) continue;
		testPt = CoordinateArrays.ptNotInList(testRing.getCoordinates(), tryShellRing.getCoordinates());
		var isContained = false;
		if (CGAlgorithms.isPointInRing(testPt, tryShellRing.getCoordinates())) isContained = true;
		if (isContained) {
			if (minShell === null || minShellEnv.contains(tryShellEnv)) {
				minShell = tryShell;
				minShellEnv = minShell.getRing().getEnvelopeInternal();
			}
		}
	}
	return minShell;
};
function EnvelopeComparator() {}
extend$1(EnvelopeComparator.prototype, {
	compare: function (obj0, obj1) {
		var r0 = obj0;
		var r1 = obj1;
		return r0.getRing().getEnvelope().compareTo(r1.getRing().getEnvelope());
	},
	interfaces_: function () {
		return [Comparator];
	},
	getClass: function () {
		return EnvelopeComparator;
	}
});
EdgeRing.EnvelopeComparator = EnvelopeComparator;

function NodeMap$1() {
	this.nodeMap = new TreeMap();
}
extend$1(NodeMap$1.prototype, {
	find: function (coord) {
		return this.nodeMap.get(coord);
	},
	iterator: function () {
		return this.nodeMap.values().iterator();
	},
	remove: function (pt) {
		return this.nodeMap.remove(pt);
	},
	values: function () {
		return this.nodeMap.values();
	},
	add: function (n) {
		this.nodeMap.put(n.getCoordinate(), n);
		return n;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return NodeMap$1;
	}
});

function PlanarGraph$1() {
	this.edges = new HashSet();
	this.dirEdges = new HashSet();
	this.nodeMap = new NodeMap$1();
}
extend$1(PlanarGraph$1.prototype, {
	findNodesOfDegree: function (degree) {
		var nodesFound = new ArrayList();
		for (var i = this.nodeIterator(); i.hasNext(); ) {
			var node = i.next();
			if (node.getDegree() === degree) nodesFound.add(node);
		}
		return nodesFound;
	},
	dirEdgeIterator: function () {
		return this.dirEdges.iterator();
	},
	edgeIterator: function () {
		return this.edges.iterator();
	},
	remove: function () {
		if (arguments[0] instanceof Edge$1) {
			let edge = arguments[0];
			this.remove(edge.getDirEdge(0));
			this.remove(edge.getDirEdge(1));
			this.edges.remove(edge);
			edge.remove();
		} else if (arguments[0] instanceof DirectedEdge$1) {
			let de = arguments[0];
			var sym = de.getSym();
			if (sym !== null) sym.setSym(null);
			de.getFromNode().remove(de);
			de.remove();
			this.dirEdges.remove(de);
		} else if (arguments[0] instanceof Node$1) {
			let node = arguments[0];
			var outEdges = node.getOutEdges().getEdges();
			for (var i = outEdges.iterator(); i.hasNext(); ) {
				var de = i.next();
				var sym = de.getSym();
				if (sym !== null) this.remove(sym);
				this.dirEdges.remove(de);
				var edge = de.getEdge();
				if (edge !== null) {
					this.edges.remove(edge);
				}
			}
			this.nodeMap.remove(node.getCoordinate());
			node.remove();
		}
	},
	findNode: function (pt) {
		return this.nodeMap.find(pt);
	},
	getEdges: function () {
		return this.edges;
	},
	nodeIterator: function () {
		return this.nodeMap.iterator();
	},
	contains: function () {
		if (arguments[0] instanceof Edge$1) {
			let e = arguments[0];
			return this.edges.contains(e);
		} else if (arguments[0] instanceof DirectedEdge$1) {
			let de = arguments[0];
			return this.dirEdges.contains(de);
		}
	},
	add: function () {
		if (arguments[0] instanceof Node$1) {
			let node = arguments[0];
			this.nodeMap.add(node);
		} else if (arguments[0] instanceof Edge$1) {
			let edge = arguments[0];
			this.edges.add(edge);
			this.add(edge.getDirEdge(0));
			this.add(edge.getDirEdge(1));
		} else if (arguments[0] instanceof DirectedEdge$1) {
			let dirEdge = arguments[0];
			this.dirEdges.add(dirEdge);
		}
	},
	getNodes: function () {
		return this.nodeMap.values();
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return PlanarGraph$1;
	}
});

function PolygonizeGraph() {
	PlanarGraph$1.apply(this);
	this.factory = null;
	let factory = arguments[0];
	this.factory = factory;
}
inherits(PolygonizeGraph, PlanarGraph$1);
extend$1(PolygonizeGraph.prototype, {
	findEdgeRing: function (startDE) {
		var er = new EdgeRing(this.factory);
		er.build(startDE);
		return er;
	},
	computeDepthParity: function () {
		if (arguments.length === 0) {
			while (true) {
				var de = null;
				if (de === null) return null;
				this.computeDepthParity(de);
			}
		} else if (arguments.length === 1) {

		}
	},
	computeNextCWEdges: function () {
		for (var iNode = this.nodeIterator(); iNode.hasNext(); ) {
			var node = iNode.next();
			PolygonizeGraph.computeNextCWEdges(node);
		}
	},
	addEdge: function (line) {
		if (line.isEmpty()) {
			return null;
		}
		var linePts = CoordinateArrays.removeRepeatedPoints(line.getCoordinates());
		if (linePts.length < 2) {
			return null;
		}
		var startPt = linePts[0];
		var endPt = linePts[linePts.length - 1];
		var nStart = this.getNode(startPt);
		var nEnd = this.getNode(endPt);
		var de0 = new PolygonizeDirectedEdge(nStart, nEnd, linePts[1], true);
		var de1 = new PolygonizeDirectedEdge(nEnd, nStart, linePts[linePts.length - 2], false);
		var edge = new PolygonizeEdge(line);
		edge.setDirectedEdges(de0, de1);
		this.add(edge);
	},
	deleteCutEdges: function () {
		this.computeNextCWEdges();
		PolygonizeGraph.findLabeledEdgeRings(this.dirEdges);
		var cutLines = new ArrayList();
		for (var i = this.dirEdges.iterator(); i.hasNext(); ) {
			var de = i.next();
			if (de.isMarked()) continue;
			var sym = de.getSym();
			if (de.getLabel() === sym.getLabel()) {
				de.setMarked(true);
				sym.setMarked(true);
				var e = de.getEdge();
				cutLines.add(e.getLine());
			}
		}
		return cutLines;
	},
	getEdgeRings: function () {
		this.computeNextCWEdges();
		PolygonizeGraph.label(this.dirEdges, -1);
		var maximalRings = PolygonizeGraph.findLabeledEdgeRings(this.dirEdges);
		this.convertMaximalToMinimalEdgeRings(maximalRings);
		var edgeRingList = new ArrayList();
		for (var i = this.dirEdges.iterator(); i.hasNext(); ) {
			var de = i.next();
			if (de.isMarked()) continue;
			if (de.isInRing()) continue;
			var er = this.findEdgeRing(de);
			edgeRingList.add(er);
		}
		return edgeRingList;
	},
	getNode: function (pt) {
		var node = this.findNode(pt);
		if (node === null) {
			node = new Node$1(pt);
			this.add(node);
		}
		return node;
	},
	convertMaximalToMinimalEdgeRings: function (ringEdges) {
		for (var i = ringEdges.iterator(); i.hasNext(); ) {
			var de = i.next();
			var label = de.getLabel();
			var intNodes = PolygonizeGraph.findIntersectionNodes(de, label);
			if (intNodes === null) continue;
			for (var iNode = intNodes.iterator(); iNode.hasNext(); ) {
				var node = iNode.next();
				PolygonizeGraph.computeNextCCWEdges(node, label);
			}
		}
	},
	deleteDangles: function () {
		var nodesToRemove = this.findNodesOfDegree(1);
		var dangleLines = new HashSet();
		var nodeStack = new Stack();
		for (var i = nodesToRemove.iterator(); i.hasNext(); ) {
			nodeStack.push(i.next());
		}
		while (!nodeStack.isEmpty()) {
			var node = nodeStack.pop();
			PolygonizeGraph.deleteAllEdges(node);
			var nodeOutEdges = node.getOutEdges().getEdges();
			for (var i = nodeOutEdges.iterator(); i.hasNext(); ) {
				var de = i.next();
				de.setMarked(true);
				var sym = de.getSym();
				if (sym !== null) sym.setMarked(true);
				var e = de.getEdge();
				dangleLines.add(e.getLine());
				var toNode = de.getToNode();
				if (PolygonizeGraph.getDegreeNonDeleted(toNode) === 1) nodeStack.push(toNode);
			}
		}
		return dangleLines;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return PolygonizeGraph;
	}
});
PolygonizeGraph.findLabeledEdgeRings = function (dirEdges) {
	var edgeRingStarts = new ArrayList();
	var currLabel = 1;
	for (var i = dirEdges.iterator(); i.hasNext(); ) {
		var de = i.next();
		if (de.isMarked()) continue;
		if (de.getLabel() >= 0) continue;
		edgeRingStarts.add(de);
		var edges = EdgeRing.findDirEdgesInRing(de);
		PolygonizeGraph.label(edges, currLabel);
		currLabel++;
	}
	return edgeRingStarts;
};
PolygonizeGraph.getDegreeNonDeleted = function (node) {
	var edges = node.getOutEdges().getEdges();
	var degree = 0;
	for (var i = edges.iterator(); i.hasNext(); ) {
		var de = i.next();
		if (!de.isMarked()) degree++;
	}
	return degree;
};
PolygonizeGraph.deleteAllEdges = function (node) {
	var edges = node.getOutEdges().getEdges();
	for (var i = edges.iterator(); i.hasNext(); ) {
		var de = i.next();
		de.setMarked(true);
		var sym = de.getSym();
		if (sym !== null) sym.setMarked(true);
	}
};
PolygonizeGraph.label = function (dirEdges, label) {
	for (var i = dirEdges.iterator(); i.hasNext(); ) {
		var de = i.next();
		de.setLabel(label);
	}
};
PolygonizeGraph.computeNextCWEdges = function (node) {
	var deStar = node.getOutEdges();
	var startDE = null;
	var prevDE = null;
	for (var i = deStar.getEdges().iterator(); i.hasNext(); ) {
		var outDE = i.next();
		if (outDE.isMarked()) continue;
		if (startDE === null) startDE = outDE;
		if (prevDE !== null) {
			var sym = prevDE.getSym();
			sym.setNext(outDE);
		}
		prevDE = outDE;
	}
	if (prevDE !== null) {
		var sym = prevDE.getSym();
		sym.setNext(startDE);
	}
};
PolygonizeGraph.computeNextCCWEdges = function (node, label) {
	var deStar = node.getOutEdges();
	var firstOutDE = null;
	var prevInDE = null;
	var edges = deStar.getEdges();
	for (var i = edges.size() - 1; i >= 0; i--) {
		var de = edges.get(i);
		var sym = de.getSym();
		var outDE = null;
		if (de.getLabel() === label) outDE = de;
		var inDE = null;
		if (sym.getLabel() === label) inDE = sym;
		if (outDE === null && inDE === null) continue;
		if (inDE !== null) {
			prevInDE = inDE;
		}
		if (outDE !== null) {
			if (prevInDE !== null) {
				prevInDE.setNext(outDE);
				prevInDE = null;
			}
			if (firstOutDE === null) firstOutDE = outDE;
		}
	}
	if (prevInDE !== null) {
		Assert.isTrue(firstOutDE !== null);
		prevInDE.setNext(firstOutDE);
	}
};
PolygonizeGraph.getDegree = function (node, label) {
	var edges = node.getOutEdges().getEdges();
	var degree = 0;
	for (var i = edges.iterator(); i.hasNext(); ) {
		var de = i.next();
		if (de.getLabel() === label) degree++;
	}
	return degree;
};
PolygonizeGraph.findIntersectionNodes = function (startDE, label) {
	var de = startDE;
	var intNodes = null;
	do {
		var node = de.getFromNode();
		if (PolygonizeGraph.getDegree(node, label) > 1) {
			if (intNodes === null) intNodes = new ArrayList();
			intNodes.add(node);
		}
		de = de.getNext();
		Assert.isTrue(de !== null, "found null DE in ring");
		Assert.isTrue(de === startDE || !de.isInRing(), "found DE already in ring");
	} while (de !== startDE);
	return intNodes;
};

function Polygonizer() {
	this.lineStringAdder = new LineStringAdder(this);
	this.graph = null;
	this.dangles = new ArrayList();
	this.cutEdges = new ArrayList();
	this.invalidRingLines = new ArrayList();
	this.holeList = null;
	this.shellList = null;
	this.polyList = null;
	this.isCheckingRingsValid = true;
	this.extractOnlyPolygonal = null;
	this.geomFactory = null;
	if (arguments.length === 0) {
		Polygonizer.call(this, false);
	} else if (arguments.length === 1) {
		let extractOnlyPolygonal = arguments[0];
		this.extractOnlyPolygonal = extractOnlyPolygonal;
	}
}
extend$1(Polygonizer.prototype, {
	getGeometry: function () {
		if (this.geomFactory === null) this.geomFactory = new GeometryFactory();
		this.polygonize();
		if (this.extractOnlyPolygonal) {
			return this.geomFactory.buildGeometry(this.polyList);
		}
		return this.geomFactory.createGeometryCollection(GeometryFactory.toGeometryArray(this.polyList));
	},
	getInvalidRingLines: function () {
		this.polygonize();
		return this.invalidRingLines;
	},
	findValidRings: function (edgeRingList, validEdgeRingList, invalidRingList) {
		for (var i = edgeRingList.iterator(); i.hasNext(); ) {
			var er = i.next();
			if (er.isValid()) validEdgeRingList.add(er); else invalidRingList.add(er.getLineString());
		}
	},
	polygonize: function () {
		if (this.polyList !== null) return null;
		this.polyList = new ArrayList();
		if (this.graph === null) return null;
		this.dangles = this.graph.deleteDangles();
		this.cutEdges = this.graph.deleteCutEdges();
		var edgeRingList = this.graph.getEdgeRings();
		var validEdgeRingList = new ArrayList();
		this.invalidRingLines = new ArrayList();
		if (this.isCheckingRingsValid) {
			this.findValidRings(edgeRingList, validEdgeRingList, this.invalidRingLines);
		} else {
			validEdgeRingList = edgeRingList;
		}
		this.findShellsAndHoles(validEdgeRingList);
		Polygonizer.assignHolesToShells(this.holeList, this.shellList);
		Collections.sort(this.shellList, new EdgeRing.EnvelopeComparator());
		var includeAll = true;
		if (this.extractOnlyPolygonal) {
			Polygonizer.findDisjointShells(this.shellList);
			includeAll = false;
		}
		this.polyList = Polygonizer.extractPolygons(this.shellList, includeAll);
	},
	getDangles: function () {
		this.polygonize();
		return this.dangles;
	},
	getCutEdges: function () {
		this.polygonize();
		return this.cutEdges;
	},
	getPolygons: function () {
		this.polygonize();
		return this.polyList;
	},
	add: function () {
		if (hasInterface(arguments[0], Collection)) {
			let geomList = arguments[0];
			for (var i = geomList.iterator(); i.hasNext(); ) {
				var geometry = i.next();
				this.add(geometry);
			}
		} else if (arguments[0] instanceof LineString) {
			let line = arguments[0];
			this.geomFactory = line.getFactory();
			if (this.graph === null) this.graph = new PolygonizeGraph(this.geomFactory);
			this.graph.addEdge(line);
		} else if (arguments[0] instanceof Geometry) {
			let g = arguments[0];
			g.apply(this.lineStringAdder);
		}
	},
	setCheckRingsValid: function (isCheckingRingsValid) {
		this.isCheckingRingsValid = isCheckingRingsValid;
	},
	findShellsAndHoles: function (edgeRingList) {
		this.holeList = new ArrayList();
		this.shellList = new ArrayList();
		for (var i = edgeRingList.iterator(); i.hasNext(); ) {
			var er = i.next();
			er.computeHole();
			if (er.isHole()) this.holeList.add(er); else this.shellList.add(er);
		}
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return Polygonizer;
	}
});
Polygonizer.findOuterShells = function (shellList) {
	for (var i = shellList.iterator(); i.hasNext(); ) {
		var er = i.next();
		var outerHoleER = er.getOuterHole();
		if (outerHoleER !== null && !outerHoleER.isProcessed()) {
			er.setIncluded(true);
			outerHoleER.setProcessed(true);
		}
	}
};
Polygonizer.extractPolygons = function (shellList, includeAll) {
	var polyList = new ArrayList();
	for (var i = shellList.iterator(); i.hasNext(); ) {
		var er = i.next();
		if (includeAll || er.isIncluded()) {
			polyList.add(er.getPolygon());
		}
	}
	return polyList;
};
Polygonizer.assignHolesToShells = function (holeList, shellList) {
	for (var i = holeList.iterator(); i.hasNext(); ) {
		var holeER = i.next();
		Polygonizer.assignHoleToShell(holeER, shellList);
	}
};
Polygonizer.assignHoleToShell = function (holeER, shellList) {
	var shell = EdgeRing.findEdgeRingContaining(holeER, shellList);
	if (shell !== null) {
		shell.addHole(holeER);
	}
};
Polygonizer.findDisjointShells = function (shellList) {
	Polygonizer.findOuterShells(shellList);
	var isMoreToScan = null;
	do {
		isMoreToScan = false;
		for (var i = shellList.iterator(); i.hasNext(); ) {
			var er = i.next();
			if (er.isIncludedSet()) continue;
			er.updateIncluded();
			if (!er.isIncludedSet()) {
				isMoreToScan = true;
			}
		}
	} while (isMoreToScan);
};
function LineStringAdder() {
	this.p = null;
	let p = arguments[0];
	this.p = p;
}
extend$1(LineStringAdder.prototype, {
	filter: function (g) {
		if (g instanceof LineString) this.p.add(g);
	},
	interfaces_: function () {
		return [GeometryComponentFilter];
	},
	getClass: function () {
		return LineStringAdder;
	}
});
Polygonizer.LineStringAdder = LineStringAdder;

function LinearLocation() {
	this.componentIndex = 0;
	this.segmentIndex = 0;
	this.segmentFraction = 0.0;
	if (arguments.length === 0) {} else if (arguments.length === 1) {
		let loc = arguments[0];
		this.componentIndex = loc.componentIndex;
		this.segmentIndex = loc.segmentIndex;
		this.segmentFraction = loc.segmentFraction;
	} else if (arguments.length === 2) {
		let segmentIndex = arguments[0], segmentFraction = arguments[1];
		LinearLocation.call(this, 0, segmentIndex, segmentFraction);
	} else if (arguments.length === 3) {
		let componentIndex = arguments[0], segmentIndex = arguments[1], segmentFraction = arguments[2];
		this.componentIndex = componentIndex;
		this.segmentIndex = segmentIndex;
		this.segmentFraction = segmentFraction;
		this.normalize();
	} else if (arguments.length === 4) {
		let componentIndex = arguments[0], segmentIndex = arguments[1], segmentFraction = arguments[2], doNormalize = arguments[3];
		this.componentIndex = componentIndex;
		this.segmentIndex = segmentIndex;
		this.segmentFraction = segmentFraction;
		if (doNormalize) this.normalize();
	}
}
extend$1(LinearLocation.prototype, {
	getSegmentIndex: function () {
		return this.segmentIndex;
	},
	getComponentIndex: function () {
		return this.componentIndex;
	},
	isEndpoint: function (linearGeom) {
		var lineComp = linearGeom.getGeometryN(this.componentIndex);
		var nseg = lineComp.getNumPoints() - 1;
		return this.segmentIndex >= nseg || this.segmentIndex === nseg && this.segmentFraction >= 1.0;
	},
	isValid: function (linearGeom) {
		if (this.componentIndex < 0 || this.componentIndex >= linearGeom.getNumGeometries()) return false;
		var lineComp = linearGeom.getGeometryN(this.componentIndex);
		if (this.segmentIndex < 0 || this.segmentIndex > lineComp.getNumPoints()) return false;
		if (this.segmentIndex === lineComp.getNumPoints() && this.segmentFraction !== 0.0) return false;
		if (this.segmentFraction < 0.0 || this.segmentFraction > 1.0) return false;
		return true;
	},
	normalize: function () {
		if (this.segmentFraction < 0.0) {
			this.segmentFraction = 0.0;
		}
		if (this.segmentFraction > 1.0) {
			this.segmentFraction = 1.0;
		}
		if (this.componentIndex < 0) {
			this.componentIndex = 0;
			this.segmentIndex = 0;
			this.segmentFraction = 0.0;
		}
		if (this.segmentIndex < 0) {
			this.segmentIndex = 0;
			this.segmentFraction = 0.0;
		}
		if (this.segmentFraction === 1.0) {
			this.segmentFraction = 0.0;
			this.segmentIndex += 1;
		}
	},
	toLowest: function (linearGeom) {
		var lineComp = linearGeom.getGeometryN(this.componentIndex);
		var nseg = lineComp.getNumPoints() - 1;
		if (this.segmentIndex < nseg) return this;
		return new LinearLocation(this.componentIndex, nseg, 1.0, false);
	},
	getCoordinate: function (linearGeom) {
		var lineComp = linearGeom.getGeometryN(this.componentIndex);
		var p0 = lineComp.getCoordinateN(this.segmentIndex);
		if (this.segmentIndex >= lineComp.getNumPoints() - 1) return p0;
		var p1 = lineComp.getCoordinateN(this.segmentIndex + 1);
		return LinearLocation.pointAlongSegmentByFraction(p0, p1, this.segmentFraction);
	},
	getSegmentFraction: function () {
		return this.segmentFraction;
	},
	getSegment: function (linearGeom) {
		var lineComp = linearGeom.getGeometryN(this.componentIndex);
		var p0 = lineComp.getCoordinateN(this.segmentIndex);
		if (this.segmentIndex >= lineComp.getNumPoints() - 1) {
			var prev = lineComp.getCoordinateN(lineComp.getNumPoints() - 2);
			return new LineSegment(prev, p0);
		}
		var p1 = lineComp.getCoordinateN(this.segmentIndex + 1);
		return new LineSegment(p0, p1);
	},
	clamp: function (linear) {
		if (this.componentIndex >= linear.getNumGeometries()) {
			this.setToEnd(linear);
			return null;
		}
		if (this.segmentIndex >= linear.getNumPoints()) {
			var line = linear.getGeometryN(this.componentIndex);
			this.segmentIndex = line.getNumPoints() - 1;
			this.segmentFraction = 1.0;
		}
	},
	setToEnd: function (linear) {
		this.componentIndex = linear.getNumGeometries() - 1;
		var lastLine = linear.getGeometryN(this.componentIndex);
		this.segmentIndex = lastLine.getNumPoints() - 1;
		this.segmentFraction = 1.0;
	},
	compareTo: function (o) {
		var other = o;
		if (this.componentIndex < other.componentIndex) return -1;
		if (this.componentIndex > other.componentIndex) return 1;
		if (this.segmentIndex < other.segmentIndex) return -1;
		if (this.segmentIndex > other.segmentIndex) return 1;
		if (this.segmentFraction < other.segmentFraction) return -1;
		if (this.segmentFraction > other.segmentFraction) return 1;
		return 0;
	},
	clone: function () {
		return new LinearLocation(this.componentIndex, this.segmentIndex, this.segmentFraction);
	},
	toString: function () {
		return "LinearLoc[" + this.componentIndex + ", " + this.segmentIndex + ", " + this.segmentFraction + "]";
	},
	isOnSameSegment: function (loc) {
		if (this.componentIndex !== loc.componentIndex) return false;
		if (this.segmentIndex === loc.segmentIndex) return true;
		if (loc.segmentIndex - this.segmentIndex === 1 && loc.segmentFraction === 0.0) return true;
		if (this.segmentIndex - loc.segmentIndex === 1 && this.segmentFraction === 0.0) return true;
		return false;
	},
	snapToVertex: function (linearGeom, minDistance) {
		if (this.segmentFraction <= 0.0 || this.segmentFraction >= 1.0) return null;
		var segLen = this.getSegmentLength(linearGeom);
		var lenToStart = this.segmentFraction * segLen;
		var lenToEnd = segLen - lenToStart;
		if (lenToStart <= lenToEnd && lenToStart < minDistance) {
			this.segmentFraction = 0.0;
		} else if (lenToEnd <= lenToStart && lenToEnd < minDistance) {
			this.segmentFraction = 1.0;
		}
	},
	compareLocationValues: function (componentIndex1, segmentIndex1, segmentFraction1) {
		if (this.componentIndex < componentIndex1) return -1;
		if (this.componentIndex > componentIndex1) return 1;
		if (this.segmentIndex < segmentIndex1) return -1;
		if (this.segmentIndex > segmentIndex1) return 1;
		if (this.segmentFraction < segmentFraction1) return -1;
		if (this.segmentFraction > segmentFraction1) return 1;
		return 0;
	},
	getSegmentLength: function (linearGeom) {
		var lineComp = linearGeom.getGeometryN(this.componentIndex);
		var segIndex = this.segmentIndex;
		if (this.segmentIndex >= lineComp.getNumPoints() - 1) segIndex = lineComp.getNumPoints() - 2;
		var p0 = lineComp.getCoordinateN(segIndex);
		var p1 = lineComp.getCoordinateN(segIndex + 1);
		return p0.distance(p1);
	},
	isVertex: function () {
		return this.segmentFraction <= 0.0 || this.segmentFraction >= 1.0;
	},
	interfaces_: function () {
		return [Comparable];
	},
	getClass: function () {
		return LinearLocation;
	}
});
LinearLocation.getEndLocation = function (linear) {
	var loc = new LinearLocation();
	loc.setToEnd(linear);
	return loc;
};
LinearLocation.pointAlongSegmentByFraction = function (p0, p1, frac) {
	if (frac <= 0.0) return p0;
	if (frac >= 1.0) return p1;
	var x = (p1.x - p0.x) * frac + p0.x;
	var y = (p1.y - p0.y) * frac + p0.y;
	var z = (p1.z - p0.z) * frac + p0.z;
	return new Coordinate(x, y, z);
};
LinearLocation.compareLocationValues = function (componentIndex0, segmentIndex0, segmentFraction0, componentIndex1, segmentIndex1, segmentFraction1) {
	if (componentIndex0 < componentIndex1) return -1;
	if (componentIndex0 > componentIndex1) return 1;
	if (segmentIndex0 < segmentIndex1) return -1;
	if (segmentIndex0 > segmentIndex1) return 1;
	if (segmentFraction0 < segmentFraction1) return -1;
	if (segmentFraction0 > segmentFraction1) return 1;
	return 0;
};

function LinearIterator() {
	this.linearGeom = null;
	this.numLines = null;
	this.currentLine = null;
	this.componentIndex = 0;
	this.vertexIndex = 0;
	if (arguments.length === 1) {
		let linear = arguments[0];
		LinearIterator.call(this, linear, 0, 0);
	} else if (arguments.length === 2) {
		let linear = arguments[0], start = arguments[1];
		LinearIterator.call(this, linear, start.getComponentIndex(), LinearIterator.segmentEndVertexIndex(start));
	} else if (arguments.length === 3) {
		let linearGeom = arguments[0], componentIndex = arguments[1], vertexIndex = arguments[2];
		if (!hasInterface(linearGeom, Lineal)) throw new IllegalArgumentException("Lineal geometry is required");
		this.linearGeom = linearGeom;
		this.numLines = linearGeom.getNumGeometries();
		this.componentIndex = componentIndex;
		this.vertexIndex = vertexIndex;
		this.loadCurrentLine();
	}
}
extend$1(LinearIterator.prototype, {
	getComponentIndex: function () {
		return this.componentIndex;
	},
	getLine: function () {
		return this.currentLine;
	},
	getVertexIndex: function () {
		return this.vertexIndex;
	},
	getSegmentEnd: function () {
		if (this.vertexIndex < this.getLine().getNumPoints() - 1) return this.currentLine.getCoordinateN(this.vertexIndex + 1);
		return null;
	},
	next: function () {
		if (!this.hasNext()) return null;
		this.vertexIndex++;
		if (this.vertexIndex >= this.currentLine.getNumPoints()) {
			this.componentIndex++;
			this.loadCurrentLine();
			this.vertexIndex = 0;
		}
	},
	loadCurrentLine: function () {
		if (this.componentIndex >= this.numLines) {
			this.currentLine = null;
			return null;
		}
		this.currentLine = this.linearGeom.getGeometryN(this.componentIndex);
	},
	getSegmentStart: function () {
		return this.currentLine.getCoordinateN(this.vertexIndex);
	},
	isEndOfLine: function () {
		if (this.componentIndex >= this.numLines) return false;
		if (this.vertexIndex < this.currentLine.getNumPoints() - 1) return false;
		return true;
	},
	hasNext: function () {
		if (this.componentIndex >= this.numLines) return false;
		if (this.componentIndex === this.numLines - 1 && this.vertexIndex >= this.currentLine.getNumPoints()) return false;
		return true;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return LinearIterator;
	}
});
LinearIterator.segmentEndVertexIndex = function (loc) {
	if (loc.getSegmentFraction() > 0.0) return loc.getSegmentIndex() + 1;
	return loc.getSegmentIndex();
};

function LocationIndexOfPoint() {
	this.linearGeom = null;
	let linearGeom = arguments[0];
	this.linearGeom = linearGeom;
}
extend$1(LocationIndexOfPoint.prototype, {
	indexOf: function (inputPt) {
		return this.indexOfFromStart(inputPt, null);
	},
	indexOfFromStart: function (inputPt, minIndex) {
		var minDistance = Double.MAX_VALUE;
		var minComponentIndex = 0;
		var minSegmentIndex = 0;
		var minFrac = -1.0;
		var seg = new LineSegment();
		for (var it = new LinearIterator(this.linearGeom); it.hasNext(); it.next()) {
			if (!it.isEndOfLine()) {
				seg.p0 = it.getSegmentStart();
				seg.p1 = it.getSegmentEnd();
				var segDistance = seg.distance(inputPt);
				var segFrac = seg.segmentFraction(inputPt);
				var candidateComponentIndex = it.getComponentIndex();
				var candidateSegmentIndex = it.getVertexIndex();
				if (segDistance < minDistance) {
					if (minIndex === null || minIndex.compareLocationValues(candidateComponentIndex, candidateSegmentIndex, segFrac) < 0) {
						minComponentIndex = candidateComponentIndex;
						minSegmentIndex = candidateSegmentIndex;
						minFrac = segFrac;
						minDistance = segDistance;
					}
				}
			}
		}
		if (minDistance === Double.MAX_VALUE) {
			return new LinearLocation(minIndex);
		}
		var loc = new LinearLocation(minComponentIndex, minSegmentIndex, minFrac);
		return loc;
	},
	indexOfAfter: function (inputPt, minIndex) {
		if (minIndex === null) return this.indexOf(inputPt);
		var endLoc = LinearLocation.getEndLocation(this.linearGeom);
		if (endLoc.compareTo(minIndex) <= 0) return endLoc;
		var closestAfter = this.indexOfFromStart(inputPt, minIndex);
		Assert.isTrue(closestAfter.compareTo(minIndex) >= 0, "computed location is before specified minimum location");
		return closestAfter;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return LocationIndexOfPoint;
	}
});
LocationIndexOfPoint.indexOf = function (linearGeom, inputPt) {
	var locater = new LocationIndexOfPoint(linearGeom);
	return locater.indexOf(inputPt);
};
LocationIndexOfPoint.indexOfAfter = function (linearGeom, inputPt, minIndex) {
	var locater = new LocationIndexOfPoint(linearGeom);
	return locater.indexOfAfter(inputPt, minIndex);
};

function LocationIndexOfLine() {
	this.linearGeom = null;
	let linearGeom = arguments[0];
	this.linearGeom = linearGeom;
}
extend$1(LocationIndexOfLine.prototype, {
	indicesOf: function (subLine) {
		var startPt = subLine.getGeometryN(0).getCoordinateN(0);
		var lastLine = subLine.getGeometryN(subLine.getNumGeometries() - 1);
		var endPt = lastLine.getCoordinateN(lastLine.getNumPoints() - 1);
		var locPt = new LocationIndexOfPoint(this.linearGeom);
		var subLineLoc = new Array(2).fill(null);
		subLineLoc[0] = locPt.indexOf(startPt);
		if (subLine.getLength() === 0.0) {
			subLineLoc[1] = subLineLoc[0].clone();
		} else {
			subLineLoc[1] = locPt.indexOfAfter(endPt, subLineLoc[0]);
		}
		return subLineLoc;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return LocationIndexOfLine;
	}
});
LocationIndexOfLine.indicesOf = function (linearGeom, subLine) {
	var locater = new LocationIndexOfLine(linearGeom);
	return locater.indicesOf(subLine);
};

function LinearGeometryBuilder() {
	this.geomFact = null;
	this.lines = new ArrayList();
	this.coordList = null;
	this.ignoreInvalidLines = false;
	this.fixInvalidLines = false;
	this.lastPt = null;
	let geomFact = arguments[0];
	this.geomFact = geomFact;
}
extend$1(LinearGeometryBuilder.prototype, {
	getGeometry: function () {
		this.endLine();
		return this.geomFact.buildGeometry(this.lines);
	},
	getLastCoordinate: function () {
		return this.lastPt;
	},
	endLine: function () {
		if (this.coordList === null) {
			return null;
		}
		if (this.ignoreInvalidLines && this.coordList.size() < 2) {
			this.coordList = null;
			return null;
		}
		var rawPts = this.coordList.toCoordinateArray();
		var pts = rawPts;
		if (this.fixInvalidLines) pts = this.validCoordinateSequence(rawPts);
		this.coordList = null;
		var line = null;
		try {
			line = this.geomFact.createLineString(pts);
		} catch (ex) {
			if (ex instanceof IllegalArgumentException) {
				if (!this.ignoreInvalidLines) throw ex;
			} else throw ex;
		} finally {}
		if (line !== null) this.lines.add(line);
	},
	setFixInvalidLines: function (fixInvalidLines) {
		this.fixInvalidLines = fixInvalidLines;
	},
	add: function () {
		if (arguments.length === 1) {
			let pt = arguments[0];
			this.add(pt, true);
		} else if (arguments.length === 2) {
			let pt = arguments[0], allowRepeatedPoints = arguments[1];
			if (this.coordList === null) this.coordList = new CoordinateList();
			this.coordList.add(pt, allowRepeatedPoints);
			this.lastPt = pt;
		}
	},
	setIgnoreInvalidLines: function (ignoreInvalidLines) {
		this.ignoreInvalidLines = ignoreInvalidLines;
	},
	validCoordinateSequence: function (pts) {
		if (pts.length >= 2) return pts;
		var validPts = [pts[0], pts[0]];
		return validPts;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return LinearGeometryBuilder;
	}
});

function ExtractLineByLocation() {
	this.line = null;
	let line = arguments[0];
	this.line = line;
}
extend$1(ExtractLineByLocation.prototype, {
	computeLinear: function (start, end) {
		var builder = new LinearGeometryBuilder(this.line.getFactory());
		builder.setFixInvalidLines(true);
		if (!start.isVertex()) builder.add(start.getCoordinate(this.line));
		for (var it = new LinearIterator(this.line, start); it.hasNext(); it.next()) {
			if (end.compareLocationValues(it.getComponentIndex(), it.getVertexIndex(), 0.0) < 0) break;
			var pt = it.getSegmentStart();
			builder.add(pt);
			if (it.isEndOfLine()) builder.endLine();
		}
		if (!end.isVertex()) builder.add(end.getCoordinate(this.line));
		return builder.getGeometry();
	},
	computeLine: function (start, end) {
		var coordinates = this.line.getCoordinates();
		var newCoordinates = new CoordinateList();
		var startSegmentIndex = start.getSegmentIndex();
		if (start.getSegmentFraction() > 0.0) startSegmentIndex += 1;
		var lastSegmentIndex = end.getSegmentIndex();
		if (end.getSegmentFraction() === 1.0) lastSegmentIndex += 1;
		if (lastSegmentIndex >= coordinates.length) lastSegmentIndex = coordinates.length - 1;
		if (!start.isVertex()) newCoordinates.add(start.getCoordinate(this.line));
		for (var i = startSegmentIndex; i <= lastSegmentIndex; i++) {
			newCoordinates.add(coordinates[i]);
		}
		if (!end.isVertex()) newCoordinates.add(end.getCoordinate(this.line));
		if (newCoordinates.size() <= 0) newCoordinates.add(start.getCoordinate(this.line));
		var newCoordinateArray = newCoordinates.toCoordinateArray();
		if (newCoordinateArray.length <= 1) {
			newCoordinateArray = [newCoordinateArray[0], newCoordinateArray[0]];
		}
		return this.line.getFactory().createLineString(newCoordinateArray);
	},
	extract: function (start, end) {
		if (end.compareTo(start) < 0) {
			return this.reverse(this.computeLinear(end, start));
		}
		return this.computeLinear(start, end);
	},
	reverse: function (linear) {
		if (linear instanceof LineString) return linear.reverse();
		if (linear instanceof MultiLineString) return linear.reverse();
		Assert.shouldNeverReachHere("non-linear geometry encountered");
		return null;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return ExtractLineByLocation;
	}
});
ExtractLineByLocation.extract = function (line, start, end) {
	var ls = new ExtractLineByLocation(line);
	return ls.extract(start, end);
};

function LocationIndexedLine() {
	this.linearGeom = null;
	let linearGeom = arguments[0];
	this.linearGeom = linearGeom;
	this.checkGeometryType();
}
extend$1(LocationIndexedLine.prototype, {
	clampIndex: function (index) {
		var loc = index.clone();
		loc.clamp(this.linearGeom);
		return loc;
	},
	project: function (pt) {
		return LocationIndexOfPoint.indexOf(this.linearGeom, pt);
	},
	checkGeometryType: function () {
		if (!(this.linearGeom instanceof LineString || this.linearGeom instanceof MultiLineString)) throw new IllegalArgumentException("Input geometry must be linear");
	},
	extractPoint: function () {
		if (arguments.length === 1) {
			let index = arguments[0];
			return index.getCoordinate(this.linearGeom);
		} else if (arguments.length === 2) {
			let index = arguments[0], offsetDistance = arguments[1];
			var indexLow = index.toLowest(this.linearGeom);
			return indexLow.getSegment(this.linearGeom).pointAlongOffset(indexLow.getSegmentFraction(), offsetDistance);
		}
	},
	isValidIndex: function (index) {
		return index.isValid(this.linearGeom);
	},
	getEndIndex: function () {
		return LinearLocation.getEndLocation(this.linearGeom);
	},
	getStartIndex: function () {
		return new LinearLocation();
	},
	indexOfAfter: function (pt, minIndex) {
		return LocationIndexOfPoint.indexOfAfter(this.linearGeom, pt, minIndex);
	},
	extractLine: function (startIndex, endIndex) {
		return ExtractLineByLocation.extract(this.linearGeom, startIndex, endIndex);
	},
	indexOf: function (pt) {
		return LocationIndexOfPoint.indexOf(this.linearGeom, pt);
	},
	indicesOf: function (subLine) {
		return LocationIndexOfLine.indicesOf(this.linearGeom, subLine);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return LocationIndexedLine;
	}
});

function LengthIndexOfPoint() {
	this.linearGeom = null;
	let linearGeom = arguments[0];
	this.linearGeom = linearGeom;
}
extend$1(LengthIndexOfPoint.prototype, {
	indexOf: function (inputPt) {
		return this.indexOfFromStart(inputPt, -1.0);
	},
	indexOfFromStart: function (inputPt, minIndex) {
		var minDistance = Double.MAX_VALUE;
		var ptMeasure = minIndex;
		var segmentStartMeasure = 0.0;
		var seg = new LineSegment();
		var it = new LinearIterator(this.linearGeom);
		while (it.hasNext()) {
			if (!it.isEndOfLine()) {
				seg.p0 = it.getSegmentStart();
				seg.p1 = it.getSegmentEnd();
				var segDistance = seg.distance(inputPt);
				var segMeasureToPt = this.segmentNearestMeasure(seg, inputPt, segmentStartMeasure);
				if (segDistance < minDistance && segMeasureToPt > minIndex) {
					ptMeasure = segMeasureToPt;
					minDistance = segDistance;
				}
				segmentStartMeasure += seg.getLength();
			}
			it.next();
		}
		return ptMeasure;
	},
	indexOfAfter: function (inputPt, minIndex) {
		if (minIndex < 0.0) return this.indexOf(inputPt);
		var endIndex = this.linearGeom.getLength();
		if (endIndex < minIndex) return endIndex;
		var closestAfter = this.indexOfFromStart(inputPt, minIndex);
		Assert.isTrue(closestAfter >= minIndex, "computed index is before specified minimum index");
		return closestAfter;
	},
	segmentNearestMeasure: function (seg, inputPt, segmentStartMeasure) {
		var projFactor = seg.projectionFactor(inputPt);
		if (projFactor <= 0.0) return segmentStartMeasure;
		if (projFactor <= 1.0) return segmentStartMeasure + projFactor * seg.getLength();
		return segmentStartMeasure + seg.getLength();
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return LengthIndexOfPoint;
	}
});
LengthIndexOfPoint.indexOf = function (linearGeom, inputPt) {
	var locater = new LengthIndexOfPoint(linearGeom);
	return locater.indexOf(inputPt);
};
LengthIndexOfPoint.indexOfAfter = function (linearGeom, inputPt, minIndex) {
	var locater = new LengthIndexOfPoint(linearGeom);
	return locater.indexOfAfter(inputPt, minIndex);
};

function LengthLocationMap() {
	this.linearGeom = null;
	let linearGeom = arguments[0];
	this.linearGeom = linearGeom;
}
extend$1(LengthLocationMap.prototype, {
	getLength: function (loc) {
		var totalLength = 0.0;
		var it = new LinearIterator(this.linearGeom);
		while (it.hasNext()) {
			if (!it.isEndOfLine()) {
				var p0 = it.getSegmentStart();
				var p1 = it.getSegmentEnd();
				var segLen = p1.distance(p0);
				if (loc.getComponentIndex() === it.getComponentIndex() && loc.getSegmentIndex() === it.getVertexIndex()) {
					return totalLength + segLen * loc.getSegmentFraction();
				}
				totalLength += segLen;
			}
			it.next();
		}
		return totalLength;
	},
	resolveHigher: function (loc) {
		if (!loc.isEndpoint(this.linearGeom)) return loc;
		var compIndex = loc.getComponentIndex();
		if (compIndex >= this.linearGeom.getNumGeometries() - 1) return loc;
		do {
			compIndex++;
		} while (compIndex < this.linearGeom.getNumGeometries() - 1 && this.linearGeom.getGeometryN(compIndex).getLength() === 0);
		return new LinearLocation(compIndex, 0, 0.0);
	},
	getLocation: function () {
		if (arguments.length === 1) {
			let length = arguments[0];
			return this.getLocation(length, true);
		} else if (arguments.length === 2) {
			let length = arguments[0], resolveLower = arguments[1];
			var forwardLength = length;
			if (length < 0.0) {
				var lineLen = this.linearGeom.getLength();
				forwardLength = lineLen + length;
			}
			var loc = this.getLocationForward(forwardLength);
			if (resolveLower) {
				return loc;
			}
			return this.resolveHigher(loc);
		}
	},
	getLocationForward: function (length) {
		if (length <= 0.0) return new LinearLocation();
		var totalLength = 0.0;
		var it = new LinearIterator(this.linearGeom);
		while (it.hasNext()) {
			if (it.isEndOfLine()) {
				if (totalLength === length) {
					var compIndex = it.getComponentIndex();
					var segIndex = it.getVertexIndex();
					return new LinearLocation(compIndex, segIndex, 0.0);
				}
			} else {
				var p0 = it.getSegmentStart();
				var p1 = it.getSegmentEnd();
				var segLen = p1.distance(p0);
				if (totalLength + segLen > length) {
					var frac = (length - totalLength) / segLen;
					var compIndex = it.getComponentIndex();
					var segIndex = it.getVertexIndex();
					return new LinearLocation(compIndex, segIndex, frac);
				}
				totalLength += segLen;
			}
			it.next();
		}
		return LinearLocation.getEndLocation(this.linearGeom);
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return LengthLocationMap;
	}
});
LengthLocationMap.getLength = function (linearGeom, loc) {
	var locater = new LengthLocationMap(linearGeom);
	return locater.getLength(loc);
};
LengthLocationMap.getLocation = function () {
	if (arguments.length === 2) {
		let linearGeom = arguments[0], length = arguments[1];
		var locater = new LengthLocationMap(linearGeom);
		return locater.getLocation(length);
	} else if (arguments.length === 3) {
		let linearGeom = arguments[0], length = arguments[1], resolveLower = arguments[2];
		var locater = new LengthLocationMap(linearGeom);
		return locater.getLocation(length, resolveLower);
	}
};

function LengthIndexedLine() {
	this.linearGeom = null;
	let linearGeom = arguments[0];
	this.linearGeom = linearGeom;
}
extend$1(LengthIndexedLine.prototype, {
	clampIndex: function (index) {
		var posIndex = this.positiveIndex(index);
		var startIndex = this.getStartIndex();
		if (posIndex < startIndex) return startIndex;
		var endIndex = this.getEndIndex();
		if (posIndex > endIndex) return endIndex;
		return posIndex;
	},
	locationOf: function () {
		if (arguments.length === 1) {
			let index = arguments[0];
			return LengthLocationMap.getLocation(this.linearGeom, index);
		} else if (arguments.length === 2) {
			let index = arguments[0], resolveLower = arguments[1];
			return LengthLocationMap.getLocation(this.linearGeom, index, resolveLower);
		}
	},
	project: function (pt) {
		return LengthIndexOfPoint.indexOf(this.linearGeom, pt);
	},
	positiveIndex: function (index) {
		if (index >= 0.0) return index;
		return this.linearGeom.getLength() + index;
	},
	extractPoint: function () {
		if (arguments.length === 1) {
			let index = arguments[0];
			var loc = LengthLocationMap.getLocation(this.linearGeom, index);
			return loc.getCoordinate(this.linearGeom);
		} else if (arguments.length === 2) {
			let index = arguments[0], offsetDistance = arguments[1];
			var loc = LengthLocationMap.getLocation(this.linearGeom, index);
			var locLow = loc.toLowest(this.linearGeom);
			return locLow.getSegment(this.linearGeom).pointAlongOffset(locLow.getSegmentFraction(), offsetDistance);
		}
	},
	isValidIndex: function (index) {
		return index >= this.getStartIndex() && index <= this.getEndIndex();
	},
	getEndIndex: function () {
		return this.linearGeom.getLength();
	},
	getStartIndex: function () {
		return 0.0;
	},
	indexOfAfter: function (pt, minIndex) {
		return LengthIndexOfPoint.indexOfAfter(this.linearGeom, pt, minIndex);
	},
	extractLine: function (startIndex, endIndex) {
		var lil = new LocationIndexedLine(this.linearGeom);
		var startIndex2 = this.clampIndex(startIndex);
		var endIndex2 = this.clampIndex(endIndex);
		var resolveStartLower = startIndex2 === endIndex2;
		var startLoc = this.locationOf(startIndex2, resolveStartLower);
		var endLoc = this.locationOf(endIndex2);
		return ExtractLineByLocation.extract(this.linearGeom, startLoc, endLoc);
	},
	indexOf: function (pt) {
		return LengthIndexOfPoint.indexOf(this.linearGeom, pt);
	},
	indicesOf: function (subLine) {
		var locIndex = LocationIndexOfLine.indicesOf(this.linearGeom, subLine);
		var index = [LengthLocationMap.getLength(this.linearGeom, locIndex[0]), LengthLocationMap.getLength(this.linearGeom, locIndex[1])];
		return index;
	},
	interfaces_: function () {
		return [];
	},
	getClass: function () {
		return LengthIndexedLine;
	}
});

const factory = new GeometryFactory();
const isSimpleOp = new IsSimpleOp();

function toLineString (coordinates) {
  return factory.createLineString(coordinates.map(c => new Coordinate(c[0], c[1])))
}

function toCoordinate (c) {
  return new Coordinate(c[0], c[1])
}

function toPoint (c) {
  return factory.createPoint(new Coordinate(c[0], c[1]))
}

function polyToCoordss (poly) {
  const cs = lineStringToCoords(poly.getExteriorRing());
  return [cs]
}

function lineStringToCoords (ls) {
  return ls.getCoordinates().map(c => [c.x, c.y])
}

function isSimple (coordinates) {
  const lineString = toLineString(coordinates);
  return isSimpleOp.isSimpleLinearGeometry(lineString)
}

function relate (cs1, cs2) {
  const ls1 = toLineString(cs1);
  const ls2 = toLineString(cs2);
  return RelateOp.relate(ls1, ls2, BoundaryNodeRule.ENDPOINT_BOUNDARY_RULE)
}

function intersects$1 (cs1, cs2) {
  const ls1 = toLineString(cs1);
  const ls2 = toLineString(cs2);
  return RelateOp.intersects(ls1, ls2)
}

function equals (c1, c2) {
  return c1[0] === c2[0] && c1[1] === c2[1]
}

function signedArea (shell) {
  if (shell.length < 3) {
    return 0
  }
  let sum = 0;
  let x;
  let y1;
  let y2;
  let p1 = shell[0];
  let p2 = shell[1];
  const x0 = p1[0];
  for (let i = 2; i < shell.length; i++) {
    let p3 = shell[i];
    x = p2[0] - x0;
    y1 = p3[1];
    y2 = p1[1];
    sum += x * (y2 - y1);
    p1 = p2;
    p2 = p3;
  }
  return sum / 2
}

function azimuth (a, b) {
  let d;

  if (a[0] === b[0]) {
    if (a[1] < b[1]) d = 0.0;
    else if (a[1] > b[1]) d = Math.PI;
    else throw new Error('same coordinate')
    return d
  }

  if (a[1] === b[1]) {
    if (a[0] < b[0]) d = Math.PI / 2;
    else if (a[0] > b[0]) d = Math.PI + (Math.PI / 2);
    else throw new Error('same coordinate')
    return d
  }

  if (a[0] < b[0]) {
    if (a[1] < b[1]) {
      d = Math.atan(Math.abs(a[0] - b[0]) / Math.abs(a[1] - b[1]));
    } else {
      d = Math.atan(Math.abs(a[1] - b[1]) / Math.abs(a[0] - b[0])) + (Math.PI / 2);
    }
  } else {
    if (a[1] > b[1]) {
      d = Math.atan(Math.abs(a[0] - b[0]) / Math.abs(a[1] - b[1])) + Math.PI;
    } else {
      d = Math.atan(Math.abs(a[1] - b[1]) / Math.abs(a[0] - b[0])) + (Math.PI + (Math.PI / 2));
    }
  }

  return d
}

function polygonize (css) {
  const lss = css.map(toLineString);
  const polygonizer = new Polygonizer();
  lss.forEach(ls => polygonizer.add(ls));
  const polys = polygonizer.getPolygons();
  if (polys.size() === 0) {
    throw new Error('Could not polygonize edges - invalid topology?')
  }
  return polyToCoordss(polys.get(0))
}

function split (coordinates, coordinate) {
  const ls = toLineString(coordinates);
  const c = toCoordinate(coordinate);
  const lil = new LengthIndexedLine(ls);
  const splitIndex = lil.project(c);
  const ls1 = lil.extractLine(lil.getStartIndex(), splitIndex);
  const ls2 = lil.extractLine(splitIndex, lil.getEndIndex());
  const cs1 = lineStringToCoords(ls1);
  const cs2 = lineStringToCoords(ls2);
  return [cs1, cs2]
}

function isLeft (c0, c1, c2) {
  return ((c1[0] - c0[0]) * (c2[1] - c0[1])) - ((c2[0] - c0[0]) * (c1[1] - c0[1]))
}

function distance (c, cs) {
  const point = toPoint(c);
  const lineString = toLineString(cs);
  return DistanceOp.distance(point, lineString)
}

function pointInPoly (c, shell) {
  return calcWindingNumber(c, shell) !== 0
}

function calcWindingNumber (c, shell) {
  let wn = 0;
  for (let i = 0; i < shell.length - 1; i++) {
    const va = shell[i];
    const vb = shell[i + 1];
    if (va[1] <= c[1]) {
      if (vb[1] > c[1]) {
        const l = isLeft(va, vb, c);
        if (l > 0) wn++;
        else if (l === 0) return 0
      }
    } else {
      if (vb[1] <= c[1]) {
        const l = isLeft(va, vb, c);
        if (l < 0) wn--;
        else if (l === 0) return 0
      }
    }
  }
  return wn
}

class SpatialError extends Error {}

/** @module */

/**
 * Edge definition
 *
 * @typedef {Object} Edge
 * @property {number} id Edge ID
 * @property {module:node~Node} start
 * @property {module:node~Node} end
 * @property {module:coordinate~Coordinate[]} coordinates Coordinates
 * @property {module:edge~Edge} nextLeft
 * @property {module:edge~Edge} nextRight
 * @property {module:face~Face} leftFace
 * @property {module:face~Face} rightFace
 * @property {number} minX Minimum X of bounds
 * @property {number} maxY Maximum Y of bounds
 * @property {number} minX Minimum X of bounds
 * @property {number} maxY Maximum Y of bounds
 */

console.debug = console.log;
console.debug = function () {};

/**
 * @param {module:edge~Edge} e
 * @param {boolean} d
 * @return {number}
 * @private
 */
function sid (e, d) {
  return d ? e.id : -e.id
}

/**
 * @param {module:edge~Edge} e
 * @return {string}
 * @private
 */


function getEdgeByPoint (topo, c, tol) {
  const result = topo.edgesTree.search({
    minX: c[0] - tol,
    minY: c[1] - tol,
    maxX: c[0] + tol,
    maxY: c[1] + tol
  });

  const candidates = result.filter(e => distance(c, e.coordinates) < tol);

  // TODO: throw exception on more than one candidate?

  return candidates
}

function getEdgesByLine (topo, cs) {
  const xs = cs.map(c => c[0]);
  const ys = cs.map(c => c[1]);

  const bounds = {
    minX: Math.min(...xs),
    minY: Math.min(...ys),
    maxX: Math.max(...xs),
    maxY: Math.max(...ys)
  };

  const edges = topo.edgesTree.search(bounds)
    .filter(e => intersects$1(cs, e.coordinates));

  return edges
}

/**
 * Adds an isolated edge defined by geometry alinestring to a topology connecting two existing isolated nodes anode and anothernode and returns the edge id of the new edge.
 *
 * @param {module:topo~Topo} topo
 * @param {module:node~Node} start
 * @param {module:node~Node} end
 * @param {module:coordinate~Coordinate[]} coordinates
 * @return {module:edge~Edge}
 */
function addIsoEdge (topo, start, end, coordinates) {
  const xs = coordinates.map(c => c[0]);
  const ys = coordinates.map(c => c[1]);

  const edge = {
    id: topo.edgesSeq,
    start,
    end,
    coordinates,
    nextLeft: { id: 0 },
    nextRight: { id: 0 },
    leftFace: { id: -1 },
    rightFace: { id: -1 },
    minX: Math.min(...xs),
    minY: Math.min(...ys),
    maxX: Math.max(...xs),
    maxY: Math.max(...ys)
  };

  if (start === end) {
    throw new SpatialError('start and end node cannot be the same as it would not construct an isolated edge')
  }

  if (!start.face || !end.face) {
    throw new SpatialError('not isolated node')
  }

  if (start.face !== end.face) {
    throw new SpatialError('nodes in different faces')
  }

  if (!equals(start.coordinate, coordinates[0])) {
    throw new SpatialError('start node not geometry start point')
  }

  if (!equals(end.coordinate, coordinates[coordinates.length - 1])) {
    throw new SpatialError('end node not geometry end point')
  }

  if (!isSimple(coordinates)) {
    throw new SpatialError('curve not simple')
  }

  checkEdgeCrossing(topo, start, end, edge);

  edge.leftFace = end.face;
  edge.nextLeft = edge;
  edge.nextLeftDir = false;
  edge.nextRight = edge;
  edge.nextRightDir = true;

  delete start.face;
  delete end.face;

  insertEdge(topo, edge);
  trigger(topo, 'addedge', edge);

  return edge
}

function checkEdgeCrossing (topo, start, end, edge) {
  const check = (e1, e2) => {
    if (e1 === e2) {
      return
    }
    const im = relate(e1.coordinates, e2.coordinates);
    if (im.matches('1FFF*FFF2')) {
      throw new SpatialError('coincident edge ' + e1.id)
    }
    if (im.matches('1********')) {
      throw new SpatialError('geometry intersects edge ' + e1.id)
    }
    if (im.matches('T********')) {
      throw new SpatialError('geometry crosses edge ' + e1.id)
    }
  };
  topo.edgesTree.search(edge).forEach(e => check(e, edge));
}

function getEdgeByNode (topo, node) {
  if (node.length) {
    return topo.edges.filter(e => node.some(n => n === e.start) || node.some(n => n === e.end))
  } else {
    return topo.edges.filter(e => e.start === node || e.end === node)
  }
}

function findAdjacentEdges (topo, node, data, other, edge) {
  data.nextCW = data.nextCCW = { id: 0 };
  data.cwFace = data.ccwFace = { id: -1 };

  let minaz, maxaz, azdif;

  if (other) {
    azdif = other.az - data.az;
    if (azdif < 0) azdif += 2 * Math.PI;
    minaz = maxaz = azdif;
    console.debug(`Other edge end has cwFace=${other.cwFace.id} and ccwFace=${other.ccwFace.id}`);
  } else {
    minaz = maxaz = -1;
  }

  console.debug(`Looking for edges incident to node ${node.id} and adjacent to azimuth ${data.az}`);

  const edges = getEdgeByNode(topo, node);

  console.debug(`getEdgeByNode returned ${edges.length} edges, minaz=${minaz}, maxaz=${maxaz}`);

  edges.forEach(e => {
    if (e === edge) {
      return
    }

    if (e.coordinates.length < 2) {
      throw new Error(`corrupted topo: edge ${e.id} does not have two distinct points`)
    }

    if (e.start === node) {
      const p1 = e.coordinates[0];
      const p2 = e.coordinates[1];
      console.debug(`edge ${e.id} starts on node ${node.id}, edgeend is ${p1[0]},${p1[1]}-${p2[0]},${p2[1]}`);
      const az = azimuth(p1, p2);
      azdif = az - data.az;
      console.debug(`azimuth of edge ${e.id}: ${az} (diff: ${azdif})`);
      if (azdif < 0) azdif += 2 * Math.PI;
      if (minaz === -1) {
        minaz = maxaz = azdif;
        data.nextCW = data.nextCCW = e;
        data.nextCWDir = data.nextCCWDir = true;
        data.cwFace = e.leftFace;
        data.ccwFace = e.rightFace;
        console.debug(`new nextCW and nextCCW edge is ${e.id}, outgoing, with face_left ${e.leftFace.id} and face_right ${e.rightFace.id} (face_right is new ccwFace, face_left is new cwFace)`);
      } else {
        if (azdif < minaz) {
          data.nextCW = e;
          data.nextCWDir = true;
          data.cwFace = e.leftFace;
          console.debug(`new nextCW edge is ${e.id}, outgoing, with face_left ${e.leftFace.id} and face_right ${e.rightFace.id} (previous had minaz=${minaz}, face_left is new cwFace)`);
          minaz = azdif;
        } else if (azdif > maxaz) {
          data.nextCCW = e;
          data.nextCCWDir = true;
          data.ccwFace = e.rightFace;
          console.debug(`new nextCCW edge is ${e.id}, outgoing, with face_left ${e.leftFace.id} and face_right ${e.rightFace.id} (previous had maxaz=${maxaz}, face_right is new ccwFace)`);
          maxaz = azdif;
        }
      }
    }

    if (e.end === node) {
      const p1 = e.coordinates[e.coordinates.length - 1];
      const p2 = e.coordinates[e.coordinates.length - 2];
      console.debug(`edge ${e.id} ends on node ${node.id}, edgeend is ${p1[0]},${p1[1]}-${p2[0]},${p2[1]}`);
      const az = azimuth(p1, p2);
      azdif = az - data.az;
      console.debug(`azimuth of edge ${e.id}: ${az} (diff: ${azdif})`);
      if (azdif < 0) azdif += 2 * Math.PI;
      if (minaz === -1) {
        minaz = maxaz = azdif;
        data.nextCW = data.nextCCW = e;
        data.nextCWDir = data.nextCCWDir = false;
        data.cwFace = e.rightFace;
        data.ccwFace = e.leftFace;
        console.debug(`new nextCW and nextCCW edge is ${e.id}, incoming, with face_left ${e.leftFace.id} and face_right ${e.rightFace.id} (face_right is new cwFace, face_left is new ccwFace)`);
      } else {
        if (azdif < minaz) {
          data.nextCW = e;
          data.nextCWDir = false;
          data.cwFace = e.rightFace;
          console.debug(`new nextCW edge is ${e.id}, incoming, with face_left ${e.leftFace.id} and face_right ${e.rightFace.id} (previous had minaz=${minaz}, face_right is new cwFace)`);
          minaz = azdif;
        } else if (azdif > maxaz) {
          data.nextCCW = e;
          data.nextCCWDir = false;
          data.ccwFace = e.leftFace;
          console.debug(`new nextCCW edge is ${e.id}, outgoing, from start point, with face_left ${e.leftFace.id} and face_right ${e.rightFace.id} (previous had maxaz=${maxaz}, face_left is new ccwFace)`);
          maxaz = azdif;
        }
      }
    }
  });

  console.debug(`edges adjacent to azimuth ${data.az} (incident to node ${node.id}): CW:${sid(data.nextCW, data.nextCWDir)}(${minaz}) CCW:${sid(data.nextCCW, data.nextCCWDir)}(${maxaz})`);

  if (!edge && edges.length > 0 && data.cwFace !== data.ccwFace) {
    if (data.cwFace.id !== -1 && data.ccwFace.id !== -1) {
      throw new Error(`Corrupted topo: adjacent edges ${sid(data.nextCW, data.nextCWDir)} and ${sid(data.nextCCW, data.nextCCWDir)} bind different face (${data.cwFace.id} and ${data.ccwFace.id})`)
    }
  }

  return edges
}

function addEdge (topo, start, end, coordinates, modFace) {
  console.debug('addEdge called');

  if (!isSimple(coordinates)) {
    throw new SpatialError('curve not simple')
  }

  const xs = coordinates.map(c => c[0]);
  const ys = coordinates.map(c => c[1]);

  const edge = {
    id: topo.edgesSeq,
    start,
    end,
    coordinates,
    nextLeft: { id: 0 },
    nextRight: { id: 0 },
    leftFace: { id: -1 },
    rightFace: { id: -1 },
    minX: Math.min(...xs),
    minY: Math.min(...ys),
    maxX: Math.max(...xs),
    maxY: Math.max(...ys)
  };

  // TODO: remove repeated points
  // TODO: check that we haave at least two points left

  const span = {
    cwFace: { id: -1 },
    ccwFace: { id: -1 },
    az: azimuth(coordinates[0], coordinates[1])
  };

  const epan = {
    cwFace: { id: -1 },
    ccwFace: { id: -1 },
    az: azimuth(coordinates[coordinates.length - 1], coordinates[coordinates.length - 2])
  };

  const nodes = start !== end ? [start, end] : [start];

  nodes.forEach(node => {
    if (node.face) {
      if (edge.leftFace.id === -1) {
        edge.leftFace = edge.rightFace = node.face;
      } else if (edge.leftFace !== node.face) {
        throw new SpatialError(`geometry crosses an edge (endnodes in faces ${edge.leftFace.id} and ${node.face.id})`)
      }
    }
  });

  if (!equals(start.coordinate, coordinates[0])) {
    throw new SpatialError('start node not geometry start point')
  }

  if (!equals(end.coordinate, coordinates[coordinates.length - 1])) {
    throw new SpatialError('end node not geometry end point')
  }

  checkEdgeCrossing(topo, start, end, edge);

  const isClosed = start === end;
  const foundStart = findAdjacentEdges(topo, start, span, isClosed ? epan : undefined);

  let prevLeft;
  let prevLeftDir;

  if (foundStart.length > 0) {
    span.wasIsolated = false;
    if (span.nextCW.id) {
      edge.nextRight = span.nextCW;
      edge.nextRightDir = span.nextCWDir;
    } else {
      edge.nextRight = edge;
      edge.nextRightDir = false;
    }
    if (span.nextCCW.id) {
      prevLeft = span.nextCCW;
      prevLeftDir = !span.nextCCWDir;
    } else {
      prevLeft = edge;
      prevLeftDir = true;
    }
    console.debug(`New edge ${edge.id} is connected on start node, next_right is ${sid(edge.nextRight, edge.nextRightDir)}, prev_left is ${sid(prevLeft, prevLeftDir)}`);
    if (edge.rightFace.id === -1) {
      edge.rightFace = span.cwFace;
    }
    if (edge.leftFace.id === -1) {
      edge.leftFace = span.ccwFace;
    }
  } else {
    span.wasIsolated = true;
    edge.nextRight = edge;
    edge.nextRightDir = !isClosed;
    prevLeft = edge;
    prevLeftDir = isClosed;
    console.debug(`New edge ${edge.id} is isolated on start node, next_right is ${sid(edge.nextRight, edge.nextRightDir)}, prev_left is ${sid(prevLeft, prevLeftDir)}`);
  }

  const foundEnd = findAdjacentEdges(topo, end, epan, isClosed ? span : undefined);

  let prevRight;
  let prevRightDir;

  if (foundEnd.length > 0) {
    epan.wasIsolated = false;
    if (epan.nextCW.id) {
      edge.nextLeft = epan.nextCW;
      edge.nextLeftDir = epan.nextCWDir;
    } else {
      edge.nextLeft = edge;
      edge.nextLeftDir = true;
    }
    if (epan.nextCCW.id) {
      prevRight = epan.nextCCW;
      prevRightDir = !epan.nextCCWDir;
    } else {
      prevRight = edge;
      prevRightDir = false;
    }
    console.debug(`New edge ${edge.id} is connected on end node, next_left is ${sid(edge.nextLeft, edge.nextLeftDir)}, prev_right is ${sid(prevRight, prevRightDir)}`);
    if (edge.rightFace.id === -1) {
      edge.rightFace = span.ccwFace;
    } else if (edge.rightFace !== epan.ccwFace) {
      throw new Error(`Side-location conflict: new edge starts in face ${edge.rightFace.id} and ends in face ${epan.ccwFace.id}`)
    }
    if (edge.leftFace.id === -1) {
      edge.leftFace = span.cwFace;
    } else if (edge.leftFace !== epan.cwFace) {
      throw new Error(`Side-location conflict: new edge starts in face ${edge.leftFace.id} and ends in face ${epan.cwFace.id}`)
    }
  } else {
    epan.wasIsolated = true;
    edge.nextLeft = edge;
    edge.nextLeftDir = isClosed;
    prevRight = edge;
    prevRightDir = !isClosed;
    console.debug(`New edge ${edge.id} is isolated on end node, next_left is ${sid(edge.nextLeft, edge.nextLeftDir)}, prev_right is ${sid(prevRight, prevRightDir)}`);
  }

  if (edge.leftFace !== edge.rightFace) {
    throw new Error(`Left(${edge.leftFace.id})/right(${edge.rightFace.id}) faces mismatch: invalid topology ?`)
  } else if (edge.leftFace.id === -1) {
    throw new Error('Could not derive edge face from linked primitives: invalid topo ?')
  }

  insertEdge(topo, edge);

  if (prevLeft !== edge) {
    if (prevLeftDir) {
      prevLeft.nextLeft = edge;
      prevLeft.nextLeftDir = true;
    } else {
      prevLeft.nextRight = edge;
      prevLeft.nextRightDir = true;
    }
  }

  if (prevRight !== edge) {
    if (prevRightDir) {
      prevRight.nextLeft = edge;
      prevRight.nextLeftDir = false;
    } else {
      prevRight.nextRight = edge;
      prevRight.nextRightDir = false;
    }
  }

  if (span.wasIsolated) {
    delete start.face;
  }
  if (epan.wasIsolated) {
    delete end.face;
  }

  if (!isClosed && (epan.wasIsolated || span.wasIsolated)) {
    trigger(topo, 'addedge', edge);
    return edge
  }

  const oldFace = edge.leftFace;

  let newface1;

  if (!modFace) {
    newface1 = addFaceSplit(topo, edge, false, edge.leftFace, false);
    if (newface1 === 0) {
      console.debug('New edge does not split any face');
      trigger(topo, 'addedge', edge);
      return edge
    }
  }

  let newface = addFaceSplit(topo, edge, true, edge.leftFace, false);

  if (modFace) {
    if (newface === 0) {
      console.debug('New edge does not split any face');
      trigger(topo, 'addedge', edge);
      return edge
    }

    if (newface < 0) {
      newface = addFaceSplit(topo, edge, false, edge.leftFace, false);
      if (newface < 0) {
        trigger(topo, 'addedge', edge);
        return edge
      }
    } else {
      addFaceSplit(topo, edge, false, edge.leftFace, true);
    }
  }

  trigger(topo, 'addedge', edge);

  if (oldFace !== topo.universe && !modFace) {
    deleteFace(topo, oldFace);
    trigger(topo, 'removeface', oldFace);
  }

  return edge
}

/**
 * Add a new edge and, if in doing so it splits a face, delete the original face and replace it with two new faces.
 *
 * @param {module:topo~Topo} topo
 * @param {module:node~Node} start
 * @param {module:node~Node} end
 * @param {module:coordinate~Coordinate[]} coordinates
 * @return {module:edge~Edge}
 */
function addEdgeNewFaces (topo, start, end, coordinates) {
  return addEdge(topo, start, end, coordinates, false)
}

/**
 * Add a new edge and, if in doing so it splits a face, modify the original face and add a new face.
 *
 * @param {module:topo~Topo} topo
 * @param {module:node~Node} start
 * @param {module:node~Node} end
 * @param {module:coordinate~Coordinate[]} coordinates
 * @return {module:edge~Edge}
 */
function addEdgeModFace (topo, start, end, coordinates) {
  return addEdge(topo, start, end, coordinates, true)
}

function remEdge (topo, edge, modFace) {
  console.debug('Updating next_{right,left}_face of ring edges...');

  const { universe, edges, nodes, facesTree } = topo;

  const oldLeftFace = edge.leftFace;
  const oldRightFace = edge.rightFace;

  const edgeNodes = [];
  edgeNodes.push(edge.start);
  if (edge.end !== edge.start) {
    edgeNodes.push(edge.end);
  }
  const updEdge = getEdgeByNode(topo, edgeNodes);
  const updEdgeLeft = [];
  const updEdgeRight = [];
  let fnodeEdges = 0;
  let lnodeEdges = 0;

  updEdge.forEach(e => {
    if (e === edge) return
    if (e.start === edge.start || e.end === edge.start) fnodeEdges++;
    if (e.start === edge.end || e.end === edge.end) lnodeEdges++;
    if (e.nextLeft === edge && !e.nextLeftDir) {
      updEdgeLeft.push({
        edge: e,
        nextLeft: edge.nextLeft !== edge || !edge.nextLeftDir ? edge.nextLeft : edge.nextRight,
        nextLeftDir: edge.nextLeft !== edge || !edge.nextLeftDir ? edge.nextLeftDir : edge.nextRightDir
      });
    } else if (e.nextLeft === edge && e.nextLeftDir) {
      updEdgeLeft.push({
        edge: e,
        nextLeft: edge.nextRight !== edge || edge.nextRightDir ? edge.nextRight : edge.nextLeft,
        nextLeftDir: edge.nextRight !== edge || edge.nextRightDir ? edge.nextRightDir : edge.nextLeftDir
      });
    }

    if (e.nextRight === edge && !e.nextRightDir) {
      updEdgeRight.push({
        edge: e,
        nextRight: edge.nextLeft !== edge || !edge.nextLeftDir ? edge.nextLeft : edge.nextRight,
        nextRightDir: edge.nextLeft !== edge || !edge.nextLeftDir ? edge.nextLefttDir : edge.nextRightDir
      });
    } else if (e.nextRight === edge && e.nextRightDir) {
      updEdgeRight.push({
        edge: e,
        nextRight: edge.nextRight !== edge || edge.nextRightDir ? edge.nextRight : edge.nextLeft,
        nextRightDir: edge.nextRight !== edge || edge.nextRightDir ? edge.nextRightDir : edge.nextLeftDir
      });
    }
  });

  updEdgeLeft.forEach(ue => {
    ue.edge.nextLeft = ue.nextLeft;
    ue.edge.nextLeftDir = ue.nextLeftDir;
  });

  updEdgeRight.forEach(ue => {
    ue.edge.nextRight = ue.nextRight;
    ue.edge.nextRightDir = ue.nextRightDir;
  });

  let floodface;
  let newface = { id: -1 };

  if (oldLeftFace === oldRightFace) {
    floodface = oldRightFace;
  } else {
    if (oldLeftFace === universe || oldRightFace === universe) {
      floodface = universe;
      console.debug('floodface is universe');
    } else {
      floodface = oldRightFace;
      console.debug('floodface is ' + floodface.id);
      // TODO: merge bboxes
      if (modFace) {
        newface = floodface;
      } else {
        insertFace(topo, newface);
        floodface = newface;
      }
    }

    if (oldLeftFace !== floodface) {
      console.debug(`Updating edges leftFace to ${floodface.id} where it was ${oldLeftFace.id}`);
      edges
        .filter(e => e.leftFace === oldLeftFace)
        .forEach(e => (e.leftFace = floodface));
      edges
        .filter(e => e.rightFace === oldLeftFace)
        .forEach(e => (e.rightFace = floodface));
      nodes
        .filter(n => n.face === oldLeftFace)
        .forEach(n => (n.face = floodface));
    }

    if (oldRightFace !== floodface) {
      console.debug(`Updating edges rightFace to ${floodface.id} where it was ${oldRightFace.id}`);
      edges
        .filter(e => e.leftFace === oldRightFace)
        .forEach(e => (e.leftFace = floodface));
      edges
        .filter(e => e.rightFace === oldRightFace)
        .forEach(e => (e.rightFace = floodface));
      nodes
        .filter(n => n.face === oldRightFace)
        .forEach(n => (n.face = floodface));
    }
  }

  deleteEdge(topo, edge);

  if (!fnodeEdges) edge.start.face = floodface;

  if (edge.end !== edge.start && !lnodeEdges) edge.end.face = floodface;

  const deletedFaces = [];
  if (oldLeftFace !== oldRightFace) {
    if (oldRightFace !== floodface) deletedFaces.push(oldRightFace);
    if (oldLeftFace !== floodface) deletedFaces.push(oldLeftFace);
  }

  newface = modFace ? floodface : newface;

  deletedFaces.forEach(f => { deleteFace(topo, f); trigger(topo, 'removeface', f); });

  trigger(topo, 'removeedge', edge);
  if (newface.id !== -1) {
    facesTree.remove(newface);
    updateFaceTree(topo, newface);
  }
  trigger(topo, 'addface', newface);

  return modFace ? floodface : newface
}

function remEdgeNewFace (topo, edge) {
  return remEdge(topo, edge, false)
}

function remEdgeModFace (topo, edge) {
  return remEdge(topo, edge, true)
}

function healEdges (topo, e1, e2, modEdge) {
  return undefined
}

function modEdgeHeal (topo, e1, e2) {
  return healEdges(topo, e1, e2, true)
}

function newEdgeHeal (topo, e1, e2) {
  return healEdges(topo, e1, e2, false)
}

function modEdgeSplit (topo, edge, coordinate) {
  const { edges, edgesTree } = topo;

  const parts = split(edge.coordinates, coordinate);

  const splitCoordinate = parts[0][parts[0].length - 1];

  const node = {
    coordinate: splitCoordinate
  };

  insertNode(topo, node);

  const newedge1 = {
    start: node,
    end: edge.end,
    leftFace: edge.leftFace,
    rightFace: edge.rightFace
  };
  newedge1.nextLeft = edge.nextLeft === edge && !edge.nextLeftDir ? newedge1 : edge.nextLeft;
  newedge1.nextLeftDir = edge.nextLeft === edge && !edge.nextLeftDir ? false : edge.nextLeftDir;
  newedge1.nextRight = edge;
  newedge1.nextRightDir = false;
  newedge1.coordinates = parts[1];

  insertEdge(topo, newedge1);

  const oldEnd = edge.end;

  edge.coordinates = parts[0];
  edge.nextLeft = newedge1;
  edge.nextLeftDir = true;
  edge.end = node;
  edgesTree.remove(edge);
  const xs = edge.coordinates.map(c => c[0]);
  const ys = edge.coordinates.map(c => c[1]);
  edge.minX = Math.min(...xs);
  edge.minY = Math.min(...ys);
  edge.maxX = Math.max(...xs);
  edge.maxY = Math.max(...ys);
  edgesTree.insert(edge);

  edges
    .filter(e => e.nextRight === edge && !e.nextRightDir && e.start === oldEnd && e !== newedge1)
    .forEach(e => { e.nextRight = newedge1; e.nextRightDir = false; });

  edges
    .filter(e => e.nextLeft === edge && !e.nextLeftDir && e.end === oldEnd && e !== newedge1)
    .forEach(e => { e.nextLeft = newedge1; e.nextLeftDir = false; });

  trigger(topo, 'addnode', node);
  trigger(topo, 'addedge', newedge1);
  trigger(topo, 'modedge', edge);

  return node
}

function newEdgesSplit (topo, edge, coordinate, skipISOChecks) {
  return undefined
}

/** @module */

/**
 * Face definition
 *
 * @typedef {Object} Face
 * @property {number} id Face ID
 */

function getNodeByFace (topo, face) {
  // TODO: only within face mbr
  return topo.nodes.filter(n => n.face === face)
}

function getFaceByPoint (topo, c, tol) {
  const result = topo.facesTree.search({
    minX: c[0] - tol,
    minY: c[1] - tol,
    maxX: c[0] + tol,
    maxY: c[1] + tol
  });

  const fs = result
    .map(f => ({
      f,
      s: getFaceGeometry(topo, f)[0]
    }));

  const candidates = fs
    .filter(fs => pointInPoly(c, fs.s))
    .map(fs => fs.f);

  // TODO: throw exception on more than one candidate?

  return candidates
}

/**
 * Returns the ordered set of signed edge identifiers met by walking on an a given edge side.
 */
function getRingEdges (topo, edge, dir, limit, foundEdges) {
  foundEdges = foundEdges || [];
  foundEdges.push({ edge, dir });

  const nextEdge = dir ? edge.nextLeft : edge.nextRight;
  const nextDir = dir ? edge.nextLeftDir : edge.nextRightDir;

  if (!foundEdges.some(fe => fe.edge === nextEdge && fe.dir === nextDir)) {
    return getRingEdges(topo, nextEdge, nextDir, 0, foundEdges)
  }

  return foundEdges
}

function getEdgeByFace (topo, face, mbr) {
  return topo.edges.filter(e => e.leftFace === face || e.rightFace === face)
  // TODO: include within mbr
}

/**
 * Returns the polygon in the given topology with the specified face.
 * @param {module:topo~Topo} topo
 * @param {module:face~Face} face
 * @return {number[][][]}
 */
function getFaceGeometry (topo, face) {
  const edges = getEdgeByFace(topo, face, false);
  if (edges.length === 0) {
    return []
  } else {
    const css = edges.map(e => e.coordinates);
    return polygonize(css)
  }
}

function getInteriorEdgePoint (coordinates) {
  // TODO: too naive
  return coordinates[1]
}

/**
 * @param {module:topo~Topo} topo
 * @param {module:edge~Edge} edge
 * @param {boolean} dir
 * @param {module:face~Face} face
 * @param {boolean} mbrOnly
 * @return {module:face~Face}
 * @private
 */
function addFaceSplit (topo, edge, dir, face, mbrOnly) {
  console.debug(`addFaceSplit called on edge ${sid(edge, dir)} and face ${face.id}`);

  const universe = topo.faces[0];

  const sedges = getRingEdges(topo, edge, dir, 0);

  sedges.forEach((se, i) => console.debug(`Component ${i} in ring of edge ${edge.id} is edge ${sid(se.edge, se.dir)}`));

  if (sedges.length === 0) throw new Error('no ring edges for edge' + edge.id)

  console.debug(`getRingEdges returned ${sedges.length} edges`);

  if (sedges.some(se => se.edge === edge && se.dir === !dir)) {
    console.debug('not a ring');
    return 0
  }

  console.debug(`Edge ${sid(edge, dir)} split face ${face.id} (mbr_only:${mbrOnly})`);

  const newFace = { id: topo.facesSeq };

  // const ringEdges = sedges.map(se => se.edge).filter((elem, pos, arr) => arr.indexOf(elem) === pos)

  sedges.forEach((se, i) => {
    console.debug(`Edge ${i} in ring of edge ${sid(edge, dir)} is edge ${sid(se.edge, se.dir)}`);
  });

  const shell = sedges
    .map(e => e.dir ? e.edge.coordinates : e.edge.coordinates.slice().reverse())
    .reduce((a, b) => a.concat(b), []);

  const isccw = signedArea(shell) <= 0;
  console.debug(`Ring of edge ${edge.id} is ${isccw ? 'counter' : ''}clockwise`);

  if (face === universe) {
    if (!isccw) {
      console.debug('The left face of this clockwise ring is the universe, will not create a new face there.');
      return -1
    }
  }

  if (mbrOnly && face !== universe) {
    return -1
  }

  const newFaceIsOutside = face !== universe && !isccw;

  if (newFaceIsOutside) {
    console.debug('New face is on the outside of the ring, updating rings in former shell');
  } else {
    console.debug('New face is on the inside of the ring, updating forward edges in new ring');
  }

  const faceEdges = getEdgeByFace(topo, face, newFace);

  console.debug(`getEdgeByFace returned ${faceEdges.length} edges`);

  faceEdges.forEach(e => {
    let found = 0;
    sedges.every(se => {
      if (e === se.edge) {
        if (se.dir) {
          console.debug(`Edge ${e.id} is a forward edge of the new ring`);
          e.leftFace = newFace;
        } else {
          console.debug(`Edge ${e.id} is a backward edge of the new ring`);
          e.rightFace = newFace;
        }
        found++;
        if (found === 2) return false
      }
      return true
    });
    if (found > 0) return

    const ep = getInteriorEdgePoint(edge.coordinates);
    const contains = pointInPoly(ep, shell);

    if (newFaceIsOutside) {
      if (contains) {
        console.debug(`Edge ${e.id} contained in an hole of the new face`);
        return
      }
    } else {
      if (!contains) {
        console.debug(`Edge ${e.id} not contained in the face shell`);
        return
      }
    }

    if (e.leftFace === face) {
      console.debug(`Edge ${e.id} has new face on the left side`);
      e.leftFace = newFace;
    }

    if (e.rightFace === face) {
      console.debug(`Edge ${e.id} has new face on the right side`);
      e.rightFace = newFace;
    }
  });

  const nodes = getNodeByFace(topo, face);

  nodes.forEach(n => {
    const contains = pointInPoly(n.coordinate, shell);
    console.debug(`Node ${n.id} is ${contains ? '' : 'not '}contained in new ring, newface is ${newFaceIsOutside ? 'outside' : 'inside'}`);
    if (newFaceIsOutside) {
      if (contains) {
        console.debug(`Node ${n.id} contained in an hole of the new face`);
        return
      }
    } else {
      if (!contains) {
        console.debug(`Node ${n.id} contained in the face shell`);
        return
      }
    }
    n.face = newFace;
  });

  insertFace(topo, newFace);
  updateFaceTree(topo, newFace);

  trigger(topo, 'addface', newFace);

  return newFace
}

/** @module */

/**
 * Node definition
 *
 * @typedef {Object} Node
 * @property {number} id Node ID
 * @property {module:face~Face} face Containing face
 * @property {module:coordinate~Coordinate} coordinate Coordinate
 * @property {number} minX Minimum X of bounds
 * @property {number} maxY Maximum Y of bounds
 * @property {number} minX Minimum X of bounds
 * @property {number} maxY Maximum Y of bounds
 */

/**
 * Find the node at a point location.
 *
 * @param {module:topo~Topo} topo
 * @param {module:coordinate~Coordinate} coordinate
 * @return {module:node~Node}
 */
function getNodeByPoint (topo, coordinate) {
  const result = topo.nodesTree.search({
    minX: coordinate[0],
    minY: coordinate[1],
    maxX: coordinate[0],
    maxY: coordinate[1]
  });
  if (result.length === 0) return
  if (result.length === 1) return result[0]
  throw Error('getNodeByPoint: unexpected search result')
}

/**
 * Adds an isolated node to a face in a topology and returns the new node. If face is null, the node is still created.
 *
 * @param {module:topo~Topo} topo
 * @param {module:coordinate~Coordinate} coordinate
 * @return {module:node~Node}
 */
function addIsoNode (topo, coordinate) {
  const { nodesTree: tree, faces } = topo;

  const containingFaces = getFaceByPoint(topo, coordinate, 0);

  const node = {
    id: topo.nodesSeq,
    face: containingFaces.length === 0 ? faces[0] : containingFaces[0],
    coordinate,
    minX: coordinate[0],
    minY: coordinate[1],
    maxX: coordinate[0],
    maxY: coordinate[1]
  };

  if (!tree.collides(node)) {
    insertNode(topo, node);
    trigger(topo, 'addnode', node);
    return node
  } else {
    throw new SpatialError('coincident node')
  }
}

function removeIsoNode (topo, node) {
  if (!node.face) throw new SpatialError('not isolated node')
  deleteNode(topo, node);
  trigger(topo, 'removenode', node);
}

/** @module */

/**
 * Topology structure
 *
 * @typedef {Object} Topo
 * @property {module:node~Node[]} nodes
 * @property {Object} nodesTree
 * @property {module:edge~Edge[]} edges
 * @property {Object} edgesTree
 * @property {module:face~Face[]} faces
 * @property {Object} facesTree
 * @property {module:face~Face} universe
 * @property {function} getNodeByPoint Calls {@link module:node.getNodeByPoint} in the context of this object
 * @property {function} addIsoNode Calls {@link module:node.addIsoNode} in the context of this object
 * @property {function} removeIsoNode Calls {@link module:node.removeIsoNode} in the context of this object
 * @property {function} getEdgeByPoint Calls {@link module:edge.getEdgeByPoint} in the context of this object
 * @property {function} getEdgesByLine Calls {@link module:edge.getEdgesByLine} in the context of this object
 * @property {function} addIsoEdge Calls {@link module:edge.addIsoEdge} in the context of this object
 * @property {function} addEdgeNewFaces Calls {@link module:edge.addEdgeNewFaces} in the context of this object
 * @property {function} addEdgeModFace Calls {@link module:edge.addEdgeModFace} in the context of this object
 * @property {function} remEdgeNewFace Calls {@link module:edge.remEdgeNewFace} in the context of this object
 * @property {function} remEdgeModFace Calls {@link module:edge.remEdgeModFace} in the context of this object
 * @property {function} newEdgesSplit Calls {@link module:edge.newEdgesSplit} in the context of this object
 * @property {function} modEdgeSplit Calls {@link module:edge.modEdgeSplit} in the context of this object
 * @property {function} newEdgeHeal Calls {@link module:edge.newEdgeHeal} in the context of this object
 * @property {function} getRingEdges Calls {@link module:face.getRingEdges} in the context of this object
 * @property {function} getFaceGeometry Calls {@link module:face.getFaceGeometry} in the context of this object
 * @property {function} on Calls {@link module:topo.on} in the context of this object
 * @property {function} un Calls {@link module:topo.un} in the context of this object
 * @fires module:topo~addface
 * @fires module:topo~removeface
 * @fires module:topo~addedge
 * @fires module:topo~modedge
 * @fires module:topo~removeedge
 * @fires module:topo~addnode
 * @fires module:topo~removenode
 */

/**
 * Emitted when a face has been added to the topology.
 * @event module:topo~addface
 * @type {module:face~Face}
 */

/**
 * Emitted when a face has been removed from the topology.
 * @event module:topo~removeface
 * @type {module:face~Face}
 */

/**
 * Emitted when an edge has been added to the topology.
 * @event module:topo~addedge
 * @type {module:edge~Edge}
 */

/**
 * Emitted when an edge has been modified.
 * @event module:topo~modedge
 * @type {module:edge~Edge}
 */

/**
 * Emitted when an edge has been removed from the topology.
 * @event module:topo~removeedge
 * @type {module:edge~Edge}
 */

/**
 * Emitted when a node has been added to the topology.
 * @event module:topo~addnode
 * @type {module:node~Node}
 */

/**
 * Emitted when a node has been removed from the topology.
 * @event module:topo~removenode
 * @type {module:node~Node}
 */

/**
 * Create topology.
 *
 * @param {string} name
 * @param {number} srid
 * @param {number} tolerance
 * @return {module:topo~Topo}
 */
function createTopology (name, srid, tolerance) {
  const nodes = [];
  const nodesTree = index(16);
  const edges = [];
  const edgesTree = index(16);
  const universe = { id: 0 };
  const faces = [universe];
  const facesTree = index(16);
  const topo = {
    name,
    srid,
    tolerance,
    nodes,
    nodesSeq: 1,
    nodesTree,
    edges,
    edgesSeq: 1,
    edgesTree,
    faces,
    facesSeq: 1,
    facesTree,
    universe,
    getNodeByPoint: (...args) => getNodeByPoint(topo, ...args),
    addIsoNode: (...args) => addIsoNode(topo, ...args),
    removeIsoNode: (...args) => removeIsoNode(topo, ...args),
    getEdgeByPoint: (...args) => getEdgeByPoint(topo, ...args),
    getEdgesByLine: (...args) => getEdgesByLine(topo, ...args),
    addIsoEdge: (...args) => addIsoEdge(topo, ...args),
    addEdgeNewFaces: (...args) => addEdgeNewFaces(topo, ...args),
    addEdgeModFace: (...args) => addEdgeModFace(topo, ...args),
    remEdgeNewFace: (...args) => remEdgeNewFace(topo, ...args),
    remEdgeModFace: (...args) => remEdgeModFace(topo, ...args),
    newEdgesSplit: (...args) => newEdgesSplit(topo, ...args),
    modEdgeSplit: (...args) => modEdgeSplit(topo, ...args),
    newEdgeHeal: (...args) => newEdgeHeal(topo, ...args),
    modEdgeHeal: (...args) => modEdgeHeal(topo, ...args),
    getRingEdges: (...args) => getRingEdges(topo, ...args),
    getFaceGeometry: (...args) => getFaceGeometry(topo, ...args),
    observers: {
      'addface': [],
      'modface': [],
      'removeface': [],
      'addedge': [],
      'modedge': [],
      'removeedge': [],
      'addnode': [],
      'removenode': []
    },
    on: (...args) => on(topo, ...args),
    un: (...args) => un(topo, ...args)
  };
  return topo
}

/**
 * Registers a callback for a named event
 * @param {module:topo~Topo} topo Topology instance.
 * @param {string} name Event name.
 * @param {function} callback Callback function.
 */
function on (topo, name, callback) {
  topo.observers[name].push(callback);
}

/**
 * Unregisters a callback for a named event
 * @param {module:topo~Topo} topo Topology instance.
 * @param {string} name Event name.
 * @param {function} callback Callback function.
 */
function un (topo, name, callback) {
  const i = topo.observers[name].indexOf(callback);
  topo.observers[name].splice(i, 1);
}

function trigger (topo, name, e) {
  topo.observers[name].forEach(o => o(e));
}

function insertFace (topo, face) {
  const { faces } = topo;
  face.id = topo.facesSeq++;
  faces.push(face);
}

function updateFaceTree (topo, face) {
  const { facesTree } = topo;
  const coordinates = getFaceGeometry(topo, face);
  const xs = coordinates[0].map(c => c[0]);
  const ys = coordinates[0].map(c => c[1]);
  face.minX = Math.min(...xs);
  face.minY = Math.min(...ys);
  face.maxX = Math.max(...xs);
  face.maxY = Math.max(...ys);
  facesTree.insert(face);
}

function deleteFace (topo, face) {
  const { faces, facesTree } = topo;
  facesTree.remove(face);
  // delete faces[faces.indexOf(face)]
  faces.splice(faces.indexOf(face), 1);
}

function insertEdge (topo, edge) {
  const { edges, edgesTree } = topo;
  const xs = edge.coordinates.map(c => c[0]);
  const ys = edge.coordinates.map(c => c[1]);
  edge.id = topo.edgesSeq++;
  edge.minX = Math.min(...xs);
  edge.minY = Math.min(...ys);
  edge.maxX = Math.max(...xs);
  edge.maxY = Math.max(...ys);
  edgesTree.insert(edge);
  edges.push(edge);
}

function deleteEdge (topo, edge) {
  const { edges, edgesTree } = topo;
  edgesTree.remove(edge);
  // delete edges[edges.indexOf(edge)]
  edges.splice(edges.indexOf(edge), 1);
}

function insertNode (topo, node) {
  const { nodes, nodesTree } = topo;

  const coordinate = node.coordinate;

  node.id = topo.nodesSeq++;
  node.minX = coordinate[0];
  node.minY = coordinate[1];
  node.maxX = coordinate[0];
  node.maxY = coordinate[1];

  nodesTree.insert(node);
  nodes.push(node);
}

function deleteNode (topo, node) {
  const { nodes, nodesTree } = topo;
  nodesTree.remove(node);
  // delete nodes[nodes.indexOf(node)]
  nodes.splice(nodes.indexOf(node), 1);
}

/**
 * Single file entry point module
 * @module
 */

exports.createTopology = createTopology;

Object.defineProperty(exports, '__esModule', { value: true });

})));
