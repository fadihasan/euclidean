package org.datastructures.node;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.*;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Stream;

/*
 * Terminology
 *
 * Superlative functions always return a value.
 * Comparative functions may return null.
 * Relative functions have the highest precedence.
 * Order of precedence: relative functions, superlative functions, comparative functions.
 *
 * Superlative terms:
 *      . First
 *      . Last
 *      . Root
 *      . Most
 *
 * Comparative functions:
 *      . Next
 *      . Previous
 *      . Predecessor
 *      . Descendant
 *      . Sibling
 *
 * Relative functions:
 *      . Predecessor
 *      . Descendant
 *      . Sibling
 *
 *
 *
 * Directions:
 * . Right: right-to-left
 * . Left: left-to-right
 * . Next: right (x + 1)
 * . Previous: left (x - 1)
 * . Predecessor: up (y - 1)
 * . Descendant: down (y + 1)
 *
 *
 *
 * Examples:
 *   1 (root)
 *   | (predecessor of 2, 5 and 8)
 *   | (predecessor of 1 is null)
 *   |
 *   +-----------------------------------------------------------------------------+-----------------------------------------------------------------+
 *   |                                                                             |                                                                 |
 *   2 (next sibling is 5)                                                         5 (next sibling is 8)                                             8 (next sibling is null)
 *   | (previous sibling is null)                                                  | (previous sibling is 2)                                           (previous sibling is 5)
 *   | (left most prior to 2, 5 and 8)                                             | (predecessor of 6 and 7)                                          (right most next to 2, 5 and 8)
 *   | (left first/right last)                                                     | (first next predecessor of 4)                                     (left last/right first)
 *   | (predecessor of 3 and 4)                                                    |
 *   |                                                                             |
 *   +-------------------------------+                                             +------------------------------------------+
 *   |                               |                                             |                                          |
 *   3 (descendant of 2)             4 (last previous descendant relative to 5)    6 (first next descendant relative to 2)    7 (descendant of 5)
 *     (first descendant is null)
 *     (last descendant is null) ...
 */
/*
 * Notes:
 * . This is a hybrid solution for tree representation and traversal using doubly linked lists and node coordinates. Common tree traversal algorithms have been implemented in this class. An additional tree representation data structure (node coordinates) along with necessary related traversal algorithms have been implemented.
 * . This class contains a variety of constructors that have been implemented to ease the transition from other data structures into Node.
 */
/*
 * Notes on node coordinates:
 * . Node coordinates is a data structure which represents tree nodes using coordinates (in the plane), where the ordinate represents the depth of the node in the tree, and the abscissa represents the horizontal position of the node in the tree.
 * . This data structure, especially when used in database systems, and with the help of some simple calculations, makes it more efficient to (and not limited to) determine the boundaries of a (sub-)tree, find predecessors of a certain node at certain levels, walk the tree, eliminating the need to resort to traditional tree traversal algorithms which involve some recursive operations. However, updating the structure of a tree whose nodes are represented by this data structure is a complex operation which involves too many calculations, making this tree representation not really useful for storing trees whose structures change frequently (in comparison with traditional data structures where the predecessor/descendant relation is simply represented by a reference to the predecessor node stored in the descendant node, and where it is simply enough to change the referenced predecessor node in the descendant in order to move a sub-tree from one place to another.)
 * . Example:
 *   1 (0, 0)
 *   |
 *   +-----------------------+-----------------------+
 *   |                       |                       |
 *   2 (0, 1)                5 (2, 1)                8 (4, 1)
 *   |                       |
 *   +-----------+           +-----------+
 *   |           |           |           |
 *   3 (0, 2)    4 (1, 2)    6 (2, 2)    7 (3, 2)
 *   The order of encounter while walking the tree by applying the breadth first (left-to-right) traversal algorithm would be the following:
 *   (0, 0), (0, 1), (2, 1), (4, 1), (0, 2), (1, 2), (2, 2), (3, 2)
 *   If this tree is stored in an SQL database, all you have to do is to order the result set by the ordinate column first and then by the abscissa column (ORDER BY Y, X.)
 *   The order of encounter while walking the tree by applying the depth first (left-to-right) traversal algorithm would be the following:
 *   (0, 0), (0, 1), (0, 2), (1, 2), (2, 1), (2, 2), (3, 2), (4, 1)
 *   Again, if this tree is stored in an SQL database, all you have to do is to order the result set by the abscissa column first and then by the ordinate column (ORDER BY X, Y.)
 *   It is also possible to move from one node in the tree to another easily (depending on the requirements) by applying simple calculations.
 */
/**
 * The <code><b>Node</b></code> class represents a node in a tree and stores a reference to an object of type <code><b>N</b></code>.
 *
 * @param <N> type of elements referenced by objects of this class.
 *
 * @author Fadi Hasan.
 */
public class Node<N> implements Collection<N>, Serializable, Cloneable {
    /**
     * The object referenced by this node.
     */
    transient private N element;
    /**
     * The array of direct descendants (at the next depth level.)
     */
    @SuppressWarnings("unchecked")
    transient private Node<N>[] descendants = new Node[0];
    /**
     * The adjacent node to the right of this node at the same depth level in the tree to which this node belongs.
     */
    transient private Node<N> nextSibling;
    /**
     * The adjacent node to the left of this node at the same depth level in the tree to which this node belongs.
     */
    transient private Node<N> previousSibling;
    /**
     * The predecessor of this node.
     */
    transient private Node<N> predecessor;
    /**
     * The abscissa of this node in the plane.
     * <p/>
     * If this is the first node in the array of direct descendants, the abscissa of this node is equal to that of the predecessor's. Subsequent nodes in the array of direct descendants have an incremental abscissa with the predecessor's abscissa as the seed. The root node has an abscissa value of 0.
     */
    transient private int x = 0;
    /**
     * The ordinate of this node in the plane.
     * <p/>
     * The depth of the node in the tree is represented by this field. The root node has an ordinate value of 0.
     */
    transient private int y = 0;
    /**
     * The number of nodes descending from this node.
     * <p/>
     * Considering this node is the root of a (sub-)tree, this value represents the number of nodes in the (sub-)tree having this node as its root.
     */
    transient private int countAll = 1;
    /**
     * Preferred traversal algorithm for the tree.
     * <p/>
     * This is a pointer to pointer that is referenced by all the nodes in the tree to which this node belongs. This property is shared among all nodes, which makes it possible to change the preferred traversal algorithm from any node in the tree.
     */
    transient private ObjectReference<TraversalAlgorithm> traversalAlgorithm = new ObjectReference<>(TraversalAlgorithm.BREADTH_FIRST_LEFT);

    /**
     * Creates a node with no referenced object.
     */
    public Node() {
    }

    /**
     * Creates a node with a reference to the given object.
     *
     * @param element the object referenced by this node.
     */
    public Node(N element) {
        this(element, TraversalAlgorithm.BREADTH_FIRST_LEFT);
    }

    /**
     * Creates a node given an object and the preferred traversal algorithm.
     *
     * @param element            the object referenced by this node.
     * @param traversalAlgorithm the preferred traversal algorithm in the current tree.
     */
    public Node(N element, TraversalAlgorithm traversalAlgorithm) {
        this.traversalAlgorithm = new ObjectReference<>(traversalAlgorithm);
        this.element = element;
    }

    /**
     * Creates a node given an object and an array of direct descendants' objects.
     * <p/>
     * For each object in the given array of direct descendants' objects a new node is created and added to the array of direct descendants.
     *
     * @param element     the object referenced by this node.
     * @param descendants an array of direct descendants' objects.
     */
    @SafeVarargs
    public Node(N element, N... descendants) {
        this(element, TraversalAlgorithm.BREADTH_FIRST_LEFT, descendants);
    }

    /**
     * Creates a node given an object, the preferred traversal algorithm and an array of direct descendants' objects.
     * <p/>
     * For each object in the given array of direct descendants' objects a new node is created and added to the array of direct descendants.
     *
     * @param element            the object referenced by this node.
     * @param traversalAlgorithm the preferred traversal algorithm.
     * @param descendants        an array of direct descendants' objects.
     */
    @SafeVarargs
    @SuppressWarnings("unchecked")
    public Node(N element, TraversalAlgorithm traversalAlgorithm, N... descendants) {
        this(element, traversalAlgorithm, Stream.of(descendants).map(e -> new Node<>(e)).<Node<N>>toArray(e -> new Node[e]));
    }

    /**
     * Creates a node given an object and an array of direct descendant nodes.
     * <p/>
     * The nodes from the given array are added to the array of direct descendants.
     *
     * @param element     the object referenced by this node.
     * @param descendants an array of direct descendants.
     */
    @SafeVarargs
    public Node(N element, Node<N>... descendants) {
        this(element, TraversalAlgorithm.BREADTH_FIRST_LEFT, descendants);
    }

    /**
     * Creates a node given an object, the preferred traversal algorithm and an array of descendant nodes.
     * <p/>
     * The nodes from the given array are added to the array of direct descendants.
     *
     * @param element            the object referenced by this node.
     * @param traversalAlgorithm the preferred traversal algorithm.
     * @param descendants        an array of direct descendants.
     * @throws NullPointerException if a null node is given.
     */
    @SafeVarargs
    public Node(N element, TraversalAlgorithm traversalAlgorithm, Node<N>... descendants) {
        this(element, traversalAlgorithm);
        for (Node<N> tmp : descendants) {
            this.add(tmp);
        }
    }

    /**
     * Creates a node given an object, a generator function and a mapper function.
     * <p/>
     * <code><b>mapper</b></code> is applied to each object generated by applying <code><b>generator</b></code> to <code><b>element</b></code>, the resulting objects are referenced by nodes that are constructed and added to the array of direct descendants. This is a recursive operation that might result in a tree with a depth greater than 1.
     *
     * @param element   the object referenced by this node.
     * @param generator a function that generates elements to be referenced by descendant nodes.
     * @param mapper    a function that translates elements generated using <code><b>generator</b></code> to type <code><b>N</b></code>.
     * @param <I>       type of elements generated using <code><b>generator</b></code>.
     */
    public <I> Node(N element, Function<N, I[]> generator, Function<I, N> mapper) {
        this.element = element;
        for (I tmp : generator.apply(element)) {
            this.add(new Node<>(mapper.apply(tmp), generator, mapper));
        }
    }

    /**
     * Creates a node given an object and a generator function.
     * <p/>
     * Objects generated by applying <code><b>generator</b></code> to <code><b>element</b></code> are referenced by nodes that are constructed and added to the array of direct descendants. This is a recursive operation that might result in a tree with a depth greater than 1.
     *
     * @param element   the object referenced by this node.
     * @param generator a function that generates elements to be referenced by descendant noes.
     */
    public Node(N element, Function<N, N[]> generator) {
        this(element, generator, e -> e);
    }

    /**
     * Creates a node given an object, a generator function and a mapper function.
     * <p/>
     * <cpde><b>mapper</b></cpde> is applied to <code><b>element</b></code>, and the resulting object is referenced by the constructed node. <code><b>mapper</b></code> is applied to each object generated by applying <code><b>generator</b></code> to <code><b>element</b></code>, the resulting objects are referenced by nodes that are constructed and added to the array of direct descendants. This is a recursive operation that might result in a tree with a depth greater than 1.
     *
     * @param generator a function that generates elements to be referenced by descendant noes.
     * @param element   the object referenced by this node, after applying the given mapper function.
     * @param mapper    a function that translates elements generated using <b>generator</b> to type <b>N</b>.
     * @param <I>       type of elements generated using <code><b>generator</b></code>.
     */
    public <I> Node(Function<I, I[]> generator, I element, Function<I, N> mapper) {
        this.element = mapper.apply(element);
        for (I tmp : generator.apply(element)) {
            this.add(new Node<>(generator, tmp, mapper));
        }
    }

    /**
     * Creates a node given an object, a generator function and a mapper function.
     * <p/>
     * Objects generated by applying <code><b>generator</b></code><b>-composed-to-</b><code><b>mapper</b></code> to <b>element</b> are referenced by nodes that are constructed and added to the array of direct descendants. This is a recursive operation that might result in a tree with a depth greater than 1.
     *
     * @param generator a function that generates elements to be referenced by descendant noes.
     * @param mapper    a function that translates elements generated using <code><b>generator</b></code> to type <code><b>N</b></code>.
     * @param element   the object referenced by this node.
     * @param <I>       type of element generate using <code><b>mapper</b></code>.
     */
    public <I> Node(Function<I, N[]> generator, Function<N, I> mapper, N element) {
        this.element = element;
        for (N tmp : generator.apply(mapper.apply(element))) {
            this.add(new Node<>(generator, mapper, tmp));
        }
    }

    /**
     * Creates a node given an object, a generator function, a mapper function and the preferred traversal algorithm.
     * <p/>
     * <code><b>mapper</b></code> is applied to each object generated by applying <code><b>generator</b></code> to <code><b>element</b></code>, the resulting objects are referenced by nodes that are constructed and added to the array of direct descendants. This is a recursive operation that might result in a tree with a depth greater than 1.
     *
     * @param element            the object referenced by this node.
     * @param generator          a function that generates elements to be referenced by descendant noes.
     * @param mapper             a function that translates elements generated using <code><b>generator</b></code> to type <code><b>N</b></code>.
     * @param traversalAlgorithm the preferred traversal algorithm.
     * @param <I>                type of elements generated using <code><b>generator</b></code>.
     */
    public <I> Node(N element, Function<N, I[]> generator, Function<I, N> mapper, TraversalAlgorithm traversalAlgorithm) {
        this(element, traversalAlgorithm);
        for (I tmp : generator.apply(element)) {
            this.add(new Node<>(mapper.apply(tmp), generator, mapper));
        }
    }

    /**
     * Create a node given an object, a generator function and the preferred traversal algorithm.
     * <p/>
     * Objects generated by applying <code><b>generator</b></code> to <code><b>generator</b></code> are referenced by nodes that are created and added to the array of direct descendants. This is a recursive operation that might result in a tree with a depth greater than 1.
     *
     * @param element            the object referenced by this node.
     * @param generator          a function that generates elements to be referenced by descendant noes.
     * @param traversalAlgorithm the preferred traversal algorithm.
     */
    public Node(N element, Function<N, N[]> generator, TraversalAlgorithm traversalAlgorithm) {
        this(element, generator, e -> e, traversalAlgorithm);
    }

    /**
     * Creates a node given an object, a generator function, a mapper function and the preferred traversal algorithm.
     * <p/>
     * <cpde><b>mapper</b></cpde> is applied to <code><b>element</b></code>, and the resulting object is referenced by the constructed node. <code><b>mapper</b></code> is applied to each object generated by applying <code><b>generator</b></code> to <code><b>element</b></code>, the resulting objects are referenced by nodes that are constructed and added to the array of direct descendants. This is a recursive operation that might result in a tree with a depth greater than 1.
     *
     * @param generator          a function that generates elements to be referenced by descendant noes.
     * @param element            the object referenced by this node, after applying the given mapper function.
     * @param mapper             a function that translates elements generated using <b>generator</b> to type <b>N</b>.
     * @param traversalAlgorithm the preferred traversal algorithm.
     * @param <I>                type of elements generated using <code><b>generator</b></code>.
     */
    public <I> Node(Function<I, I[]> generator, I element, Function<I, N> mapper, TraversalAlgorithm traversalAlgorithm) {
        this(mapper.apply(element), traversalAlgorithm);
        for (I tmp : generator.apply(element)) {
            this.add(new Node<>(generator, tmp, mapper));
        }
    }

    /**
     * Creates a node given an object, a generator function, a mapper function and the preferred traversal algorithm.
     * <p/>
     * Objects generated by applying <code><b>generator</b></code><b>-composed-to-</b><code><b>mapper</b></code> to <b>element</b> are referenced by nodes that are constructed and added to the array of direct descendants. This is a recursive operation that might result in a tree with a depth greater than 1.
     *
     * @param generator          a function that generates elements to be referenced by descendant noes.
     * @param mapper             a function that translates elements generated using <code><b>generator</b></code> to type <code><b>N</b></code>.
     * @param element            the object referenced by this node.
     * @param traversalAlgorithm the preferred traversal algorithm.
     * @param <I>                type of element generate using <code><b>mapper</b></code>.
     */
    public <I> Node(Function<I, N[]> generator, Function<N, I> mapper, N element, TraversalAlgorithm traversalAlgorithm) {
        this(element, traversalAlgorithm);
        for (N tmp : generator.apply(mapper.apply(element))) {
            this.add(new Node<>(generator, mapper, tmp));
        }
    }

    /**
     * Gets this node's referenced object.
     *
     * @return the object referenced by this node, or null if this node does not hold a reference to any object.
     */
    public N getElement() {
        return this.element;
    }

    /**
     * Sets the object referenced by this node.
     *
     * @param element the object referenced by this node.
     */
    public void setElement(N element) {
        this.element = element;
    }

    /**
     * Gets the adjacent node to the right of this node at the current depth level in the tree to which this node belongs.
     *
     * @return the node to right of this node in the tree, or null if this node is the right-most node in the tree at the current depth level.
     */
    public Node<N> getNextSibling() {
        return this.nextSibling;
    }

    /**
     * Gets the adjacent node to the left of this node at the current depth level in the tree to which this node belongs.
     *
     * @return the node to left of this node in the tree, or null if this node is the left-most node in the tree at the current depth level.
     */
    public Node<N> getPreviousSibling() {
        return this.previousSibling;
    }

    /**
     * Gets the predecessor of this node (at the previous depth level.)
     *
     * @return the predecessor of this node, or null if this node is the root of the tree.
     */
    public Node<N> getPredecessor() {
        return this.predecessor;
    }

    /**
     * Gets the descendant node at the specified position in the array of direct descendants (at the next depth level.)
     *
     * @param i the index of the descendant node to return.
     * @return the direct descendant node at the specified position.
     * @throws IndexOutOfBoundsException if the index is out of range.
     */
    public Node<N> getDescendant(int i) {
        if (i < 0 || i > this.descendants.length - 1) {
            throw new IndexOutOfBoundsException(String.valueOf(i));
        }
        return this.descendants[i];
    }

    /**
     * Gets the number of direct descendants (at the next depth level.)
     *
     * @return the number of direct descendants (at the next depth level.)
     */
    public int countDescendants() {
        return this.descendants.length;
    }

    /**
     * Gets the number of descendants of this node.
     * <p/>
     * This function returns the number of nodes in the (sub-)tree having this node as its root.
     *
     * @return the number of descendants of this node, or 1 if this node has no descendants.
     */
    @Override
    public int size() {
        return this.countAll;
    }

    /**
     * Gets the abscissa of this node in the plane.
     *
     * @return the abscissa of this node in the plane.
     */
    public int getX() {
        return this.x;
    }

    /**
     * Gets the ordinate of this node in the plane.
     *
     * @return the ordinate of this node in the plane.
     */
    public int getY() {
        return this.y;
    }

    /**
     * Gets the preferred traversal algorithm for the tree tho which this node belongs.
     *
     * @return the preferred traversal algorithm for the tree to which this node belongs.
     */
    public TraversalAlgorithm getTraversalAlgorithm() {
        return this.traversalAlgorithm.object;
    }

    /**
     * Sets the preferred traversal algorithm for three tree to which this node belongs.
     *
     * @param traversalAlgorithm the preferred traversal algorithm for the tree to which this node belongs.
     */
    public void setTraversalAlgorithm(TraversalAlgorithm traversalAlgorithm) {
        this.traversalAlgorithm.object = traversalAlgorithm;
    }

    /**
     * Gets the first descendant node in the array of direct descendants (at the next depth level.)
     *
     * @return the descendant node at position 0 in the array of direct descendants, or null if this node has no descendants.
     */
    public Node<N> getFirstDescendant() {
        return this.descendants.length == 0 ? null : this.descendants[0];
    }

    /**
     * Gets the last descendant node in the array of direct descendants (at the next depth level.)
     *
     * @return the descendant node at the last position in the array of direct descendants, or null if this node has no descendants.
     */
    public Node<N> getLastDescendant() {
        return this.descendants.length == 0 ? null : this.descendants[this.descendants.length - 1];
    }

    /**
     * Gets the first sibling in the tree (at the current depth level.)
     *
     * @return the left-most node in the tree at the current depth level.
     */
    public Node<N> getFirstSibling() {
        for (Node<N> tmp = this.previousSibling; tmp != null; tmp = tmp.previousSibling) {
            if (tmp.previousSibling == null) {
                return tmp;
            }
        }
        return this;
    }

    /**
     * Gets the last sibling in the tree (at the current depth level.)
     *
     * @return the right-most node in the tree at the current depth level.
     */
    public Node<N> getLastSibling() {
        for (Node<N> tmp = this.nextSibling; tmp != null; tmp = tmp.nextSibling) {
            if (tmp.nextSibling == null) {
                return tmp;
            }
        }
        return this;
    }

    /**
     * Gets the left-most descendant node at the next depth level to the right of this node.
     *
     * @return the first next descendant, or null if no sibling can be found to the right of this node at the current depth level having any descendant.
     */
    public Node<N> getFirstNextDescendant() {
        for (Node<N> tmp = this.nextSibling; tmp != null; tmp = tmp.nextSibling) {
            if (tmp.descendants.length > 0) {
                return tmp.descendants[0];
            }
        }
        return null;
    }

    /**
     * Gets the right-most descendant node at the next depth level to the left of this node.
     *
     * @return the last previous descendant, or null if no sibling can be found to the left of this node at the current depth level having any descendant.
     */
    public Node<N> getLastPreviousDescendant() {
        for (Node<N> tmp = this.previousSibling; tmp != null; tmp = tmp.previousSibling) {
            if (tmp.descendants.length > 0) {
                return tmp.descendants[tmp.descendants.length - 1];
            }
        }
        return null;
    }

    /**
     * Gets the left-most and closest predecessor to the right of this node having a predecessor in common with this node.
     *
     * @return the first next predecessor, or null if no predecessor of this node has a sibling to the right.
     */
    public Node<N> getFirstNextPredecessor() {
        for (Node<N> tmp = this.predecessor; tmp != null; tmp = tmp.predecessor) {
            if (tmp.nextSibling != null && tmp.nextSibling.predecessor == tmp.predecessor) {
                return tmp.nextSibling;
            }
        }
        return null;
    }

    /**
     * Gets the right-most and closest predecessor to the left of this node having a predecessor in common with this node.
     *
     * @return the last previous predecessor, or null if no predecessor of this node has a sibling to the left.
     */
    public Node<N> getLastPreviousPredecessor() {
        for (Node<N> tmp = this.predecessor; tmp != null; tmp = tmp.predecessor) {
            if (tmp.previousSibling != null && tmp.previousSibling.predecessor == tmp.predecessor) {
                return tmp.previousSibling;
            }
        }
        return null;
    }

    /**
     * Gets the furthest left-most descendant node.
     * <p/>
     * This function returns a node having an abscissa equal to this node's abscissa and the maximum possible ordinate.
     *
     * @return gets the furthest left-most node.
     */
    public Node<N> getInmostLeft() {
        Node<N> tmp = this;
        for (; tmp.descendants.length > 0; tmp = tmp.descendants[0]) ;
        return tmp;
    }

    /**
     * Gets the furthest right-most descendant node.
     * <p/>
     * This function returns a node having the greatest possible abscissa in the (sub-)tree having this node as its root and the maximum ordinate.
     *
     * @return the right-most descendant node.
     */
    public Node<N> getInmostRight() {
        Node<N> tmp = this;
        for (; tmp.descendants.length > 0; tmp = tmp.descendants[tmp.descendants.length - 1]) ;
        return tmp;
    }

    /**
     * Returns the furthest predecessor of this node.
     *
     * @return the root of the tree to which this node belongs.
     */
    public Node<N> getRoot() {
        Node<N> tmp = this;
        for (; tmp.predecessor != null; tmp = tmp.predecessor) ;
        return tmp;
    }

    /**
     * Gets the breadth of the (sub-)tree having this node as its root.
     * <p/>
     * This function returns the difference between the right-most node's abscissa and this node's abscissa plus one.
     *
     * @return the breadth of the (sub-)tree having this node as its root.
     */
    public int getBreadth() {
        return this.getInmostRight().x - this.x + 1;
    }

    /**
     * Appends a node referencing the given object to the array of direct descendants (at the next depth level.)
     * <p/>
     * This function calls {@link #add(Node)}
     *
     * @param element the object referenced by this node's last direct descendant.
     * @return true.
     */
    @Override
    public boolean add(N element) {
        return this.add(new Node<>(element));
    }

    /**
     * Appends the given node to the array of direct descendants.
     * <p/>
     * This function performs the given operations:
     * <ul>
     *     <li>Detach the given node before appending the node to the array of direct descendants.</li>
     *     <li>Update the sizes of this node and its predecessors.</li>
     *     <li>Update the abscissas of:
     *     <ol>
     *         <li>The given node.</li>
     *         <li>Descendant nodes of the given node.</li>
     *         <li>The siblings to right of this node.</li>
     *         <li>Descendants of the siblings to the right of this node.</li>
     *     </ol>
     *     </li>
     *     <li>Update the ordinates of the given node and its descendants.</li>
     *     <li>Update the preferred traversal algorithm of the given node and its descendants.</li>
     *     <li>Update next/previous sibling and predecessor connections.</li>
     * </ul>
     *
     * @param descendant the node to be appended to the list of direct descendants.
     * @return true.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if the given node is the same as this node.
     */
    public boolean add(Node<N> descendant) {
        if (descendant == null) {
            throw new NullPointerException();
        }
        if (descendant == this) {
            throw new IllegalArgumentException();
        }
        descendant.detach();
        int breadth = this.descendants.length > 0 ? descendant.getBreadth() : (breadth = descendant.getBreadth()) > 1 ? breadth - 1 : 0, dx = this.descendants.length == 0 ? this.x : this.getBreadth() + this.x;
        {
            Node[] tmp = new Node[this.descendants.length + 1];
            int i = 0;
            for (; i < this.descendants.length; tmp[i] = this.descendants[i++]) ;
            ((tmp[i] = descendant).predecessor = this).descendants = tmp;
        }
        for (Node<N> next = breadth > 0 ? descendant.nextSibling : null; next != null; next.x += breadth, next = next.nextSibling) ;
        for (Node<N> tmp = descendant.predecessor; tmp != null; tmp.countAll += descendant.countAll, tmp = tmp.predecessor) {
            for (Node<N> next = breadth > 0 ? tmp.nextSibling : null; next != null; next.x += breadth, next = next.nextSibling) ;
        }
        for (Node<N> leftMost = descendant, rightMost = leftMost, nextLeftMost = leftMost.descendants.length == 0 ? null : leftMost.descendants[0], nextRightMost = rightMost.descendants.length == 0 ? null : rightMost.descendants[rightMost.descendants.length - 1], lastLeft = this.descendants.length > 1 ? this.descendants[this.descendants.length - 2] : this.getLastPreviousDescendant(), firstRight = this.getFirstNextDescendant(); leftMost != null || firstRight != null || lastLeft != null; lastLeft = lastLeft == null ? null : lastLeft.descendants.length > 0 ? lastLeft.descendants[lastLeft.descendants.length - 1] : lastLeft.getLastPreviousDescendant(), firstRight = firstRight == null ? null : firstRight.descendants.length > 0 ? firstRight.descendants[0] : firstRight.getFirstNextDescendant()) {
            for (Node<N> tmp = leftMost; tmp != null && tmp.previousSibling != rightMost; tmp.x += dx, tmp.y = tmp.predecessor.y + 1, tmp.traversalAlgorithm = tmp.predecessor.traversalAlgorithm, tmp = tmp.nextSibling) ;
            for (Node<N> tmp = breadth > 0 ? firstRight : null; tmp != null; tmp.x += breadth, tmp = tmp.nextSibling) ;
            if (leftMost != null && lastLeft != null) {
                (leftMost.previousSibling = lastLeft).nextSibling = leftMost;
            }
            if (rightMost != null && firstRight != null) {
                (rightMost.nextSibling = firstRight).previousSibling = rightMost;
            }
            if ((leftMost = nextLeftMost) != null) {
                nextLeftMost = leftMost.descendants.length == 0 ? leftMost.getFirstNextDescendant() : leftMost.descendants[0];
            }
            if ((rightMost = nextRightMost) != null) {
                nextRightMost = rightMost.descendants.length == 0 ? rightMost.getLastPreviousDescendant() : rightMost.descendants[rightMost.descendants.length - 1];
            }
        }
        return true;
    }

    /**
     * Detaches this node from the tree to which this node belongs.
     * <p/>
     * This function performs the given operations:
     * <ul>
     *     <li>Update the sizes of this node's predecessors.</li>
     *     <li>Remove this node from the array of direct descendants of this node's predecessor.</li>
     *     <li>Reset the predecessor of this node.</li>
     *     <li>Update the abscissas of:
     *     <ol>
     *         <li>This node.</li>
     *         <li>Descendant nodes of this node.</li>
     *         <li>The siblings to the right of this node.</li>
     *         <li>Descendants of the siblings to the right of this node.</li>
     *     </ol>
     *     </li>
     *     <li>Update the ordinates of this node and its descendants.</li>
     *     <li>Update next/previous sibling connections.</li>
     * </ul>
     */
    @SuppressWarnings("unchecked")
    public void detach() {
        if (this.predecessor == null) {
            return;
        }
        int breadth = this.predecessor.descendants.length > 1 ? this.getBreadth() : (breadth = this.getBreadth()) > 1 ? breadth - 1 : 0, dx = this.x, dy = this.y;
        {
            Node[] tmp = new Node[this.predecessor.descendants.length - 1];
            for (int i = 0, j = 0; j < tmp.length; tmp[j++] = this.predecessor.descendants[i] == this ? this.predecessor.descendants[++i] : this.predecessor.descendants[i], i++) ;
            this.predecessor.descendants = tmp;
        }
        for (Node<N> tmp = this.predecessor; tmp != null; tmp.countAll -= this.countAll, tmp = tmp.predecessor) {
            for (Node<N> next = breadth > 0 ? tmp.nextSibling : null; next != null; next.x -= breadth, next = next.nextSibling) ;
        }
        ObjectReference<TraversalAlgorithm> newTraversalAlgorithm = new ObjectReference<>(this.traversalAlgorithm.getObject());
        this.predecessor = null;
        for (Node<N> leftMost = this, rightMost = this, lastLeft = this.previousSibling, firstRight = this.nextSibling; lastLeft != null || firstRight != null || leftMost != null; leftMost = leftMost == null ? null : leftMost.descendants.length > 0 ? leftMost.descendants[0] : leftMost.getFirstNextDescendant(), rightMost = rightMost == null ? null : rightMost.descendants.length > 0 ? rightMost.descendants[rightMost.descendants.length - 1] : rightMost.getLastPreviousDescendant(), firstRight = firstRight == null ? null : firstRight.descendants.length > 0 ? firstRight.descendants[0] : firstRight.getFirstNextDescendant(), lastLeft = lastLeft == null ? null : lastLeft.descendants.length > 0 ? lastLeft.descendants[lastLeft.descendants.length - 1] : lastLeft.getLastPreviousDescendant()) {
            if (rightMost != null) {
                rightMost.nextSibling = null;
            }
            if (leftMost != null) {
                leftMost.previousSibling = null;
            }
            if (firstRight != null) {
                firstRight.previousSibling = lastLeft;
            }
            if (lastLeft != null) {
                lastLeft.nextSibling = firstRight;
            }
            for (Node<N> tmp = leftMost; tmp != null; tmp.x -= dx, tmp.traversalAlgorithm = newTraversalAlgorithm, tmp.y -= dy, tmp = tmp.nextSibling) ;
            for (Node<N> tmp = breadth > 0 ? firstRight : null; tmp != null; tmp.x -= breadth, tmp = tmp.nextSibling) ;
        }
    }

    /**
     * Tells whether this node has no descendants.
     *
     * @return true if this has no descendants, false otherwise.
     */
    @Override
    public boolean isEmpty() {
        return this.countAll <= 1;
    }

    /**
     * Tells whether the given object is referenced by this node or one of its descendants.
     * <p/>
     * This function iterates over the nodes of the (sub-)tree having this node as its root using the preferred traversal algorithm for the tree to which this node belongs.
     *
     * @param o object whose presence is to be tested in the (sub-)tree having this node as its root.
     * @return true if the given object is referenced by this node or one of its descendants, false otherwise.
     */
    @Override
    public boolean contains(Object o) {
        Iterator<N> it = iterator();
        if (o == null) {
            while (it.hasNext())
                if (it.next() == null)
                    return true;
        } else {
            while (it.hasNext())
                if (o.equals(it.next()))
                    return true;
        }
        return false;
    }

    /**
     * Returns an iterator over the nodes of the (sub-)tree having this node as its root.
     * <p/>
     * This function returns an iterator over the nodes of the (sub-)tree having this node as its root using the preferred traversal algorithm for the tree to which this node belongs.
     *
     * @return an iterator over the nodes of the (sub-)tree having this node as its root.
     */
    @Override
    public Iterator<N> iterator() {
        return new NodeIterator<>(this, this.traversalAlgorithm.object);
    }

    /**
     * Returns an array containing the objects referenced by this node and its descendants sorted by the order of encounter of the nodes applying the preferred traversal algorithm for the tree to which this node belongs.
     * <p/>
     * This function calls {@link Node#toArray(Object[])}.
     *
     * @return an array containing the elements referenced by the (sub-)tree having this node as its root.
     */
    @Override
    public Object[] toArray() {
        return this.toArray(new Object[0]);
    }

    /**
     * Returns an array containing the objects referenced by this node and its descendants sorted by the order of encounter of the nodes using the preferred traversal algorithm for the tree to which this node belongs.
     *
     * @param a the array in which the objects referenced by the (sub-)tree having this node as its root are stored, if it is big enough, otherwise, a new array of the same runtime type is allocated for this purpose.
     * @return an array containing the objects referenced by this node and its descendants.
     */
    @Override
    @SuppressWarnings("unchecked")
    public <M> M[] toArray(M[] a) {
        M[] result = Objects.requireNonNull(a).length < this.countAll ? Arrays.copyOf(a, this.countAll) : a;
        Iterator<N> iterator = iterator();
        for (int i = 0; i < this.countAll; result[i++] = (M) iterator.next()) ;
        return result;
    }

    /**
     * Removes all nodes referencing the given object from (sub-)tree having this node as its root.
     * <p/>
     * This function traverses the nodes of the (sub-)tree having this node as its root using an object of type {@link NodeIterator} which applies the preferred traversal algorithm. Nodes referencing objects in the given collection will be removed by calling {@link Node#detach()}.
     *
     * @param o the referenced object.
     * @return if at least one node was removed as a result of a call to this function.
     */
    @Override
    public boolean remove(Object o) {
        boolean flag = false;
        for (Iterator<N> iterator = iterator(); iterator.hasNext(); ) {
            if (Objects.equals(iterator.next(), o)) {
                iterator.remove();
                flag = true;
            }
        }
        return flag;
    }

    /**
     * Returns true if all the objects in the given collection are referenced by nodes in the (sub-)tree having this node as its root.
     *
     * @param c collection of objects to be checked.
     * @return if all the objects in the given collection are referenced by nodes in the (sub-)tree having this node as its root.
     * @throws NullPointerException if the given collection is null.
     */
    @Override
    public boolean containsAll(Collection<?> c) {
        for (Object tmp : Objects.requireNonNull(c)) {
            if (!contains(tmp)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Appends nodes referencing the objects in the given collection to the array of direct descendants.
     * <p/>
     * This function calls {@link Node#add(Node)} for each object in the given collection.
     *
     * @param c collection of objects to be referenced by direct descendant nodes.
     * @return true.
     * @throws NullPointerException if the given collection is null.
     */
    @Override
    public boolean addAll(Collection<? extends N> c) {
        Objects.requireNonNull(c).forEach(e -> this.add(e));
        return true;
    }

    /**
     * Removes all descendant nodes referencing objects in the given collection from the (sub-)tree having this node as its root.
     *
     * @param c collection of objects to be checked.
     * @return true if the structure of three having this node as its root changed as a result of a call to this function, false otherwise.
     * @throws NullPointerException if the given collection is null.
     */
    @Override
    public boolean removeAll(Collection<?> c) {
        Objects.requireNonNull(c);
        boolean flag = false;
        for (Iterator<N> iterator = iterator(); iterator.hasNext(); ) {
            if (c.contains(iterator.next())) {
                iterator.remove();
                flag = true;
            }
        }
        return flag;
    }

    /**
     * Removes all nodes from the (sub-)tree having this node as its root not referencing any object from the given collection.
     * <p/>
     * This function traverses the nodes of the (sub-)tree having this node as its root using an object of type {@link NodeIterator} which applies the preferred traversal algorithm. Nodes not referencing objects in the given collection will be removed by calling {@link Node#detach()}.
     *
     * @param c collection of objects to be checked.
     * @return true if the structure of the (sub-)tree having this node as its root changed as a result of a call to this function, false otherwise.
     * @throws NullPointerException if the given collection is null.
     */
    @Override
    public boolean retainAll(Collection<?> c) {
        Objects.requireNonNull(c);
        boolean flag = false;
        for (Iterator<N> iterator = iterator(); iterator.hasNext(); ) {
            if (!c.contains(iterator.next())) {
                iterator.remove();
                flag = true;
            }
        }
        return flag;
    }

    /**
     * Removes all direct descendant nodes from the array of direct descendants.
     */
    @Override
    public void clear() {
        for (Node<N> descendant : this.descendants) {
            descendant.detach();
        }
    }

    /*
     * Traversal.
     */
    /**
     * This function traverses to the next node in the tree in a breadth-first left-to-right order of encounter and returns the encountered node.
     *
     * @return the next node in the tree in a breadth-first left-to-right order of encounter, or null if this node is the last node in that order.
     */
    public Node<N> getBreadthFirstLeftNext() {
        if (this.nextSibling != null) {
            return this.nextSibling;
        }
        Node<N> tmp = this.getFirstSibling();
        return tmp.descendants.length == 0 ? tmp.getFirstNextDescendant() : tmp.descendants[0];
    }

    /**
     * This function traverses to the next node in the tree in a breadth-first right-to-left order of encounter and returns the encountered node.
     *
     * @return the next node in the tree in a breadth-first right-to-left order encounter, or null if this node is the last node in that order.
     */
    public Node<N> getBreadthFirstRightNext() {
        if (this.previousSibling != null) {
            return this.previousSibling;
        }
        Node<N> tmp = this.getLastSibling();
        return tmp.descendants.length == 0 ? tmp.getLastPreviousDescendant() : tmp.descendants[tmp.descendants.length - 1];
    }

    /**
     * This function traverses to the next node in the tree in a depth-first left-to-right order of encounter and returns the encountered node.
     *
     * @return the next node in the tree in a depth-first left-to-right order of encounter, or null if this node is the last node in that order.
     */
    public Node<N> getDepthFirstLeftNext() {
        return this.descendants.length == 0 ? this.nextSibling == null ? this.getFirstNextPredecessor() : this.nextSibling.predecessor == this.predecessor ? this.nextSibling : this.getFirstNextPredecessor() : this.descendants[0];
    }

    /**
     * This function traverses to the next node in the tree in a depth-first right-to-left order of encounter and returns the encountered node.
     *
     * @return the next node in the tree in a depth-first right-to-left order of encounter, or null if this node is the last node in that order.
     */
    public Node<N> getDepthFirstRightNext() {
        return this.descendants.length == 0 ? this.previousSibling == null ? this.getLastPreviousPredecessor() : this.previousSibling.predecessor == this.predecessor ? this.previousSibling : this.getLastPreviousPredecessor() : this.descendants[this.descendants.length - 1];
    }

    /*
     * Search.
     */
    /**
     * Tells whether the given node belongs to the tree to which this node belongs.
     *
     * @param element the node to be checked.
     * @return true if both nodes belong to same tree, false otherwise.
     * @throws NullPointerException if the given node is null.
     */
    public boolean containsNode(Node<N> element) {
        Node<N> tmp1, tmp2;
        if (Objects.requireNonNull(element).y > this.y) {
            tmp1 = element;
            tmp2 = this;
        } else {
            tmp1 = this;
            tmp2 = element;
        }
        for (; tmp1 != null && tmp1.y > tmp2.y; tmp1 = tmp1.predecessor) ;
        for (; tmp1 != null && tmp2 != null; tmp1 = tmp1.predecessor, tmp2 = tmp2.predecessor) {
            if (tmp1 == tmp2) {
                return true;
            }
        }
        return false;
    }

    /**
     * Tells whether the given object is referenced by a node that follows this node in a breadth-first left-to-right order of encounter in the tree to which this node belongs.
     *
     * @param element the object to be checked.
     * @return true if a node referencing the given object is found following this node in a breadth-first left-to-right order of encounter in the tree, false otherwise.
     */
    public boolean containsBreadthFirstLeftNext(N element) {
        return this.findBreadthFirstLeftNext(element) != null;
    }

    /**
     * Tells whether the given object is referenced by a node that follows this node in a breadth-first right-to-left order of encounter in the tree to which this node belongs.
     *
     * @param element the object to be checked.
     * @return true if a node referencing the given object is found following this node in a breadth-first right-to-left order of encounter in the tree, false otherwise.
     */
    public boolean containsBreadthFirstRightNext(N element) {
        return this.findBreadthFirstRightNext(element) != null;
    }

    /**
     * Tells whether the given object is referenced by a node that follows this node in a depth-first left-to-right order of encounter in the tree to which this node belongs.
     *
     * @param element the object to be checked.
     * @return true if a node referencing the given object is found following this node in a depth-first left-to-right order of encounter in the tree, false otherwise.
     */
    public boolean containsDepthFirstLeftNext(N element) {
        return this.findDepthFirstLeftNext(element) != null;
    }

    /**
     * Tells whether the given object is referenced by a node that follows this node in a depth-first right-to-left order of encounter in the tree to which this node belongs.
     *
     * @param element the object to be checked.
     * @return true if a node referencing the given object is found following this node in a depth-first right-to-left order of encounter in the tree, false otherwise.
     */
    public boolean containsDepthFirstRightNext(N element) {
        return this.findDepthFirstRightNext(element) != null;
    }

    /**
     * Returns the first encountered node that references the given object and follows this node in a breadth-first left-to-right order of encounter in the tree to which this node belongs.
     *
     * @param element the object to be searched.
     * @return the node referencing the given object following this node in a breadth-first left-to-right order of encounter in the tree.
     */
    public Node<N> findBreadthFirstLeftNext(N element) {
        return this.findBreadthFirstLeftNext(e -> e.equals(element));
    }

    /**
     * Returns the first encountered node that references the given object and follows this node in a breadth-first right-to-left order of encounter in the tree to which this node belongs.
     *
     * @param element the object to be searched.
     * @return the node referencing the given object following this node in a breadth-first right-to-left order of encounter in the tree.
     */
    public Node<N> findBreadthFirstRightNext(N element) {
        return this.findBreadthFirstRightNext(e -> e.equals(element));
    }

    /**
     * Returns the first encountered node that references the given object and follows this node in a depth-first left-to-right order of encounter in the tree to which this node belongs.
     *
     * @param element the object to be searched.
     * @return the node referencing the given object following this node in a depth-first left-to-right order of encounter in the tree.
     */
    public Node<N> findDepthFirstLeftNext(N element) {
        return this.findDepthFirstLeftNext(e -> e.equals(element));
    }

    /**
     * Returns the first encountered node that references the given object and follows this node in a depth-first right-to-left order of encounter in the tree to which this node belongs.
     *
     * @param element the object to be searched.
     * @return the node referencing the given object following this node in a depth-first right-to-left order of encounter in the tree.
     */
    public Node<N> findDepthFirstRightNext(N element) {
        return this.findDepthFirstRightNext(e -> e.equals(element));
    }

    /**
     * Returns the first encountered node that references an object that is equal to the given object, according to the given comparator function, and follows this node in a breadth-first left-to-right order of encounter in the tree to which this node belongs.
     *
     * @param element    the object to compare.
     * @param comparator a comparator function applied to the given object and each object referenced by encountered nodes.
     * @return the node referencing an object that is equal to the given object following this node in a breadth-first left-to-right order of encounter in the tree.
     */
    public Node<N> findBreadthFirstLeftNext(N element, Comparator<N> comparator) {
        return this.findBreadthFirstLeftNext(e -> comparator.compare(e, element) == 0);
    }

    /**
     * Returns the first encountered node that references an object that is equal to the given object, according to the given comparator function, and follows this node in a breadth-first right-te-left order of encounter in the tree to which this node belongs.
     *
     * @param element    the object to compare.
     * @param comparator a comparator function applied to the given object and each object referenced by encountered nodes.
     * @return the node referencing an object that is equal to the given object following this node in a breadth-first right-to-left order of encounter in the tree.
     */
    public Node<N> findBreadthFirstRightNext(N element, Comparator<N> comparator) {
        return this.findBreadthFirstRightNext(e -> comparator.compare(e, element) == 0);
    }

    /**
     * Returns the first encountered node that references an object that is equal to the given object, according to the given comparator function, and follows this node in a depth-first left-to-right order of encounter in the tree to which this node belongs.
     *
     * @param element    the object to compare.
     * @param comparator a comparator function applied to the given object and each object referenced by encountered nodes.
     * @return the node referencing an object that is equal to the given object following this node in a depth-first left-to-right order of encounter in the tree.
     */
    public Node<N> findDepthFirstLeftNext(N element, Comparator<N> comparator) {
        return this.findDepthFirstLeftNext(e -> comparator.compare(e, element) == 0);
    }

    /**
     * Returns the first encountered node that references an object that is equal to the given object, according to the given comparator function, and follows this node in a depth-first right-to-left order of encounter in the tree to which this node belongs.
     *
     * @param element    the object to compare.
     * @param comparator a comparator function applied to the given object and each object referenced by encountered nodes.
     * @return the node referencing an object that is equal to the given object following this node in a depth-first right-to-left order of encounter in the tree.
     */
    public Node<N> findDepthFirstRightNext(N element, Comparator<N> comparator) {
        return this.findDepthFirstRightNext(e -> comparator.compare(e, element) == 0);
    }

    /**
     * Returns the first encountered node referencing an object that matches the given predicate and follows this node in a breadth-first left-to-right order of encounter in the tree to which this node belongs.
     *
     * @param predicate the predicate that is applied to each encountered node's referenced object.
     * @return the node referencing an object that satisfies the given predicate following this node in a breadth-first left-to-right order of encounter in the tree.
     */
    public Node<N> findBreadthFirstLeftNext(Predicate<N> predicate) {
        for (Node<N> tmp = this; tmp != null; tmp = tmp.getBreadthFirstLeftNext()) {
            if (predicate.test(tmp.element)) {
                return tmp;
            }
        }
        return null;
    }

    /**
     * Returns the first encountered node referencing an object that matches the given predicate and follows this node in a breadth-first right-to-left order of encounter in the tree to which this node belongs.
     *
     * @param predicate the predicate that is applied to each encountered node's referenced object.
     * @return the node referencing an object that satisfies the given predicate following this node in a breadth-first right-to-left order of encounter in the tree.
     */
    public Node<N> findBreadthFirstRightNext(Predicate<N> predicate) {
        for (Node<N> tmp = this; tmp != null; tmp = tmp.getBreadthFirstRightNext()) {
            if (predicate.test(tmp.element)) {
                return tmp;
            }
        }
        return null;
    }

    /**
     * Returns the first encountered node referencing an object that matches the given predicate and follows this node in a depth-first left-to-right order of encounter in the tree to which this node belongs.
     *
     * @param predicate the predicate that is applied to each encountered node's referenced object.
     * @return the node referencing an object that satisfies the given predicate following this node in a depth-first left-to-right order of encounter in the tree.
     */
    public Node<N> findDepthFirstLeftNext(Predicate<N> predicate) {
        for (Node<N> tmp = this; tmp != null; tmp = tmp.getDepthFirstLeftNext()) {
            if (predicate.test(tmp.element)) {
                return tmp;
            }
        }
        return null;
    }

    /**
     * Returns the first encountered node referencing an object that matches the given predicate and follows this node in a depth-first right-to-left order of encounter in the tree to which this node belongs.
     *
     * @param predicate the predicate that is applied to each encountered node's referenced object.
     * @return the node referencing an object that satisfies the given predicate following this node in a depth-first right-to-left order of encounter in the tree.
     */
    public Node<N> findDepthFirstRightNext(Predicate<N> predicate) {
        for (Node<N> tmp = this; tmp != null; tmp = tmp.getDepthFirstRightNext()) {
            if (predicate.test(tmp.element)) {
                return tmp;
            }
        }
        return null;
    }

    /*
     * sub-tree.
     */
    /*
     * Traversal
     */
    /**
     * Gets the adjacent node to the right of this node at the current depth level in the (sub-)tree to which this node belongs.
     *
     * @param root the root node of the (sub-)tree to be traversed.
     * @return the node to right of this node in the (sub-)tree, or null if this node is the right-most node in the (sub-)tree at the current depth level.
     */
    public Node<N> getNextSibling(Node<N> root) {
        return this.nextSibling == null ? null : root.nextSibling == null ? this.nextSibling : this.nextSibling.x < root.nextSibling.x ? this.nextSibling : null;
    }

    /**
     * Gets the adjacent node to the left of this node at the current depth level in the (sub-)tree to which this node belongs.
     *
     * @param root the root node of the (sub-)tree to be traversed.
     * @return the node to left of this node in the (sub-)tree, or null if this node is the left-most node in the (sub-)tree at the current depth level.
     */
    public Node<N> getPreviousSibling(Node<N> root) {
        return this.previousSibling == null ? null : root.previousSibling == null ? this.previousSibling : this.previousSibling.x >= root.x ? this.previousSibling : null;
    }

    /**
     * Tells whether this node is a descendant of the given node.
     *
     * @param root the node to be checked.
     * @return true if this node is a descendant of the given node or if the given node is null, false otherwise.
     */
    public boolean isDescendantOf(Node<N> root) {
        if (root == null) {
            return true;
        }
        for (Node<N> tmp = this; tmp != null && tmp.y >= root.y; tmp = tmp.predecessor) {
            if (tmp == root) {
                return true;
            }
        }
        return false;
    }

    /**
     * Tells whether this node is a predecessor of the given node.
     *
     * @param descendant the node to be checked.
     * @return true if this node is a predecessor of the given node.
     * @throws NullPointerException if the given node is null.
     */
    public boolean isPredecessorOf(Node<N> descendant) {
        return descendant.isDescendantOf(this);
    }

    /**
     * Gets the first sibling at the current depth level in the (sub-)tree having the given node as its root.
     *
     * @param root the root node of the (sub-)tree to be traversed.
     * @return the left-most node at the current depth level in the (sub-)tree having the given node as its root.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> getFirstSibling(Node<N> root) {
        this.validateRoot(root);
        for (Node<N> tmp = this; root.previousSibling == null || tmp.x > root.previousSibling.x; tmp = tmp.previousSibling) {
            if ((root.previousSibling != null && tmp.previousSibling != null && tmp.previousSibling.x < root.x) || tmp.previousSibling == null) {
                return tmp;
            }
        }
        return this;
    }

    /**
     * Gets the last sibling at the current depth level in the (sub-)tree having the given node as its root.
     *
     * @param root the root node of the (sub-)tree to be traversed.
     * @return the right-most node at the current depth level in the (sub-)tree having the given node as its root.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> getLastSibling(Node<N> root) {
        this.validateRoot(root);
        for (Node<N> tmp = this; root.nextSibling == null || tmp.x < root.nextSibling.x; tmp = tmp.nextSibling) {
            if ((root.nextSibling != null && tmp.nextSibling != null && tmp.nextSibling.x >= root.nextSibling.x) || tmp.nextSibling == null) {
                return tmp;
            }
        }
        return this;
    }

    /**
     * Gets the left-most descendant node at the next depth level in the (sub-)tree having the given node as its root to the right of the (sub-)tree having this node as its root.
     *
     * @param root the root node of the (sub-)tree to be traversed.
     * @return the first next descendant, or null if no node can be found to the right of this node at the current depth level having any descendant.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> getFirstNextDescendant(Node<N> root) {
        this.validateRoot(root);
        for (Node<N> tmp = this.nextSibling; tmp != null && (root.nextSibling == null || tmp.x < root.nextSibling.x); tmp = tmp.nextSibling) {
            if (tmp.descendants.length > 0) {
                return tmp.descendants[0];
            }
        }
        return null;
    }

    /**
     * Gets the right-most descendant node at the next depth level in the (sub-)tree having the given node as its root to the left of the (sub-)tree having this node as its root.
     *
     * @param root the root node of the (sub-)tree to be traversed.
     * @return the last previous descendant, or null if no node can be found to the left of this node at the current depth level having any descendant.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> getLastPreviousDescendant(Node<N> root) {
        this.validateRoot(root);
        for (Node<N> tmp = this.previousSibling; tmp != null && tmp.x >= root.x; tmp = tmp.previousSibling) {
            if (tmp.descendants.length > 0) {
                return tmp.descendants[tmp.descendants.length - 1];
            }
        }
        return null;
    }

    /**
     * Gets the left-most and closest (depth-first order of encounter) predecessor to the right of this node having a predecessor in common with this node in the (sub-)tree having the given node as its root.
     *
     * @param root the root node of the (sub-)tree to be traversed.
     * @return the first next predecessor, or null if no predecessor of this node has a sibling to the right.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> getFirstNextPredecessor(Node<N> root) {
        this.validateRoot(root);
        for (Node<N> tmp = this.predecessor; tmp != null && tmp.y > root.y; tmp = tmp.predecessor) {
            if (tmp.nextSibling != null && tmp.nextSibling.predecessor == tmp.predecessor) {
                return tmp.nextSibling;
            }
        }
        return null;
    }

    /**
     * Gets the right-most and closest (depth-first order of encounter) predecessor to the left of this node having a predecessor in common with this node in the tree having the given node as its root.
     *
     * @param root the root node of the tree to be traversed.
     * @return the last previous predecessor, or null if no predecessor of this node has a sibling to the left.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> getLastPreviousPredecessor(Node<N> root) {
        this.validateRoot(root);
        for (Node<N> tmp = this.predecessor; tmp != null && tmp.y > root.y; tmp = tmp.predecessor) {
            if (tmp.previousSibling != null && tmp.previousSibling.predecessor == tmp.predecessor) {
                return tmp.previousSibling;
            }
        }
        return null;
    }

    /**
     * This function traverses to the next node in a breadth-first left-to-right order of encounter in the (sub-)tree having the given node as its root and returns the encountered node.
     *
     * @param root the root node of the (sub-)tree to be traversed.
     * @return the next node in a breadth-first left-to-right order of encounter in the (sub-)tree having the given node as its root, or null if this node is the last node.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> getBreadthFirstLeftNext(Node<N> root) {
        this.validateRoot(root);
        if (this.nextSibling != null && this.nextSibling.isDescendantOf(root)) {
            return this.nextSibling;
        }
        Node<N> tmp = this.getFirstSibling(root);
        return tmp.descendants.length == 0 ? tmp.getFirstNextDescendant(root) : tmp.descendants[0];
    }

    /**
     * This function traverses to the next node in a breadth-first right-to-left order of encounter in the (sub-)tree having the given node as its root and returns the encountered node.
     *
     * @param root the root node of the (sub-)tree to be traversed.
     * @return the next node in a breadth-first right-to-left order of encounter in the (sub-)tree having the given node as its root, or null if this node is the last node.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> getBreadthFirstRightNext(Node<N> root) {
        this.validateRoot(root);
        if (this.previousSibling != null && this.previousSibling.isDescendantOf(root)) {
            return this.previousSibling;
        }
        Node<N> tmp = this.getLastSibling(root);
        return tmp.descendants.length == 0 ? tmp.getLastPreviousDescendant(root) : tmp.descendants[tmp.descendants.length - 1];
    }

    /**
     * This function traverses to the next node in a depth-first left-to-right order of encounter in the (sub-)tree having the given node as its root and returns the encountered node.
     *
     * @param root the root node of the (sub-)tree to be traversed.
     * @return the next node in a depth-first left-to-right order of encounter in the (sub-)tree having the given node as its root, or null if this node is the last node.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> getDepthFirstLeftNext(Node<N> root) {
        this.validateRoot(root);
        return this.descendants.length == 0 ? this.nextSibling == null ? this.getFirstNextPredecessor(root) : this.nextSibling.predecessor == this.predecessor ? this.nextSibling : this.getFirstNextPredecessor(root) : this.descendants[0];
    }

    /**
     * This function traverses to the next node in a depth-first right-to-left order of encounter in the (sub-)tree having the given node as its root and returns the encountered node.
     *
     * @param root the root node of the (sub-)tree to be traversed.
     * @return the next node in a depth-first right-to-left order of encounter in the (sub-)tree having the given node as its root, or null if this node is the last node.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> getDepthFirstRightNext(Node<N> root) {
        this.validateRoot(root);
        return this.descendants.length == 0 ? this.previousSibling == null ? this.getLastPreviousPredecessor(root) : this.previousSibling.predecessor == this.predecessor ? this.previousSibling : this.getLastPreviousPredecessor(root) : this.descendants[this.descendants.length - 1];
    }

    /**
     * Validates whether this node is a descendant of the given node.
     *
     * @param root the node to be checked.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public void validateRoot(Node<N> root) {
        if (!this.isDescendantOf(Objects.requireNonNull(root))) {
            throw new IllegalArgumentException();
        }
    }

    /*
     * Search.
     */
    /**
     * Returns the first encountered node that references the given object and follows this node in a breadth-first left-to-right order of encounter in the (sub-)tree having the given node as its root.
     *
     * @param element the object to be searched.
     * @param root    the root node of the (sub-)tree to be traversed.
     * @return the node referencing the given object following this node in a breadth-first left-to-right order of encounter in the (sub-)tree having the given node as its root.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> findBreadthFirstLeftNext(N element, Node<N> root) {
        return this.findBreadthFirstLeftNext(e -> e.equals(element), root);
    }

    /**
     * Returns the first encountered node that references the given object and follows this node in a breadth-first right-to-left order of encounter in the (sub-)tree having the given node as its root.
     *
     * @param element the object to be searched.
     * @param root    the root node of the (sub-)tree to be traversed.
     * @return the node referencing the given object following this node in a breadth-first right-to-left order of encounter in the (sub-)tree having the given node as its root.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> findBreadthFirstRightNext(N element, Node<N> root) {
        return this.findBreadthFirstRightNext(e -> e.equals(element), root);
    }

    /**
     * Returns the first encountered node that references the given object and follows this node in a depth-first right-to-left order of encounter in the (sub-)tree having the given node as its root.
     *
     * @param element the object to be searched.
     * @param root    the root node of the (sub-)tree to be traversed.
     * @return the node referencing the given object following this node in a breadth-first depth-to-left order of encounter in the (sub-)tree having the given node as its root.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> findDepthFirstLeftNext(N element, Node<N> root) {
        return this.findDepthFirstLeftNext(e -> e.equals(element), root);
    }

    /**
     * Returns the first encountered node that references the given object and follows this node in a depth-first right-to-left order of encounter in the (sub-)tree having the given node as its root.
     *
     * @param element the object to be searched.
     * @param root    the root node of the (sub-)tree to be traversed.
     * @return the node referencing the given object following this node in a depth-first right-to-left order of encounter in the (sub-)tree having the given node as its root.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> findDepthFirstRightNext(N element, Node<N> root) {
        return this.findDepthFirstRightNext(e -> e.equals(element), root);
    }

    /**
     * Returns the first encountered node that references an object that is equal to the given object, according to the given comparator function, and follows this node in a breadth-first left-to-right order of encounter in the (sub-)tree having the given node as its root.
     *
     * @param element    the object to be searched.
     * @param comparator a comparator function applied to the given object and each object referenced by encountered nodes.
     * @param root       the root node of the (sub-)tree to be traversed.
     * @return the node referencing an object that is equal to the given object following this node in a breadth-first left-to-right order of encounter in the (sub-)tree having the given node as its root.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> findBreadthFirstLeftNext(N element, Comparator<N> comparator, Node<N> root) {
        return this.findBreadthFirstLeftNext(e -> comparator.compare(e, element) == 0, root);
    }

    /**
     * Returns the first encountered node that references an object that is equal to the given object, according to the given comparator function, and follows this node in a breadth-first right-to-left order of encounter in the (sub-)tree having the given node as its root.
     *
     * @param element    the object to be searched.
     * @param comparator a comparator function applied to the given object and each object referenced by encountered nodes.
     * @param root       the root node of the (sub-)tree to be traversed.
     * @return the node referencing an object that is equal to the given object following this node in a breadth-first right-to-left order of encounter in the (sub-)tree having the given node as its root.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> findBreadthFirstRightNext(N element, Comparator<N> comparator, Node<N> root) {
        return this.findBreadthFirstRightNext(e -> comparator.compare(e, element) == 0, root);
    }

    /**
     * Returns the first encountered node that references an object that is equal to the given object, according to the given comparator function, and follows this node in a depth-first left-to-right order of encounter in the (sub-)tree having the given node as its root.
     *
     * @param element    the object to be searched.
     * @param comparator a comparator function applied to the given object and each object referenced by encountered nodes.
     * @param root       the root node of the (sub-)tree to be traversed.
     * @return the node referencing an object that is equal to the given object following this node in a depth-first left-to-right order of encounter in the (sub-)tree having the given node as its root.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> findDepthFirstLeftNext(N element, Comparator<N> comparator, Node<N> root) {
        return this.findDepthFirstLeftNext(e -> comparator.compare(e, element) == 0, root);
    }

    /**
     * Returns the first encountered node that references an object that is equal to the given object, according to the given comparator function, and follows this node in a depth-first right-to-left order of encounter in the (sub-)tree having the given node as its root.
     *
     * @param element    the object to be searched.
     * @param comparator a comparator function applied to the given object and each object referenced by encountered nodes.
     * @param root       the root node of the (sub-)tree to be traversed.
     * @return the node referencing an object that is equal to the given object following this node in a depth-first right-to-left order of encounter in the (sub-)tree having the given node as its root.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> findDepthFirstRightNext(N element, Comparator<N> comparator, Node<N> root) {
        return this.findDepthFirstRightNext(e -> comparator.compare(e, element) == 0, root);
    }

    /**
     * Returns the first encountered node referencing an object that matches the given predicate and follows this node in a breadth-first left-to-right order of encounter in the (sub-)tree having the given node as its root.
     *
     * @param predicate the predicate that is applied to each encountered node.
     * @param root      the root node of the (sub-)tree to be traversed.
     * @return the node referencing an object that matches the given predicate following this node in a breadth-first left-to-right order of encounter in the (sub-)tree having the given node as its root.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> findBreadthFirstLeftNext(Predicate<N> predicate, Node<N> root) {
        for (Node<N> tmp = this; tmp != null; tmp = tmp.getBreadthFirstLeftNext(root)) {
            if (predicate.test(tmp.element)) {
                return tmp;
            }
        }
        return null;
    }

    /**
     * Returns the first encountered node referencing an object that matches the given predicate and follows this node in a breadth-first right-to-left order of encounter in the (sub-)tree having the given node as its root.
     *
     * @param predicate the predicate that is applied to each encountered node.
     * @param root      the root node of the (sub-)tree to be traversed.
     * @return the node referencing an object that matches the given predicate following this node in a breadth-first right-to-left order of encounter in the (sub-)tree having the given node as its root.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> findBreadthFirstRightNext(Predicate<N> predicate, Node<N> root) {
        for (Node<N> tmp = this; tmp != null; tmp = tmp.getBreadthFirstRightNext(root)) {
            if (predicate.test(tmp.element)) {
                return tmp;
            }
        }
        return null;
    }

    /**
     * Returns the first encountered node referencing an object that matches the given predicate and follows this node in a depth-first left-to-right order of encounter in the (sub-)tree having the given node as its root.
     *
     * @param predicate the predicate that is applied to each encountered node.
     * @param root      the root node of the (sub-)tree to be traversed.
     * @return the node referencing an object that matches the given predicate following this node in a depth-first left-to-right order of encounter in the (sub-)tree having the given node as its root.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> findDepthFirstLeftNext(Predicate<N> predicate, Node<N> root) {
        for (Node<N> tmp = this; tmp != null; tmp = tmp.getDepthFirstLeftNext(root)) {
            if (predicate.test(tmp.element)) {
                return tmp;
            }
        }
        return null;
    }

    /**
     * Returns the first encountered node referencing an object that matches the given predicate and follows this node in a depth-first right-to-left order of encounter in the (sub-)tree having the given node as its root.
     *
     * @param predicate the predicate that is applied to each encountered node.
     * @param root      the root node of the (sub-)tree to be traversed.
     * @return the node referencing an object that matches the given predicate following this node in a depth-first right-to-left order of encounter in the (sub-)tree having the given node as its root.
     * @throws NullPointerException     if the given node is null.
     * @throws IllegalArgumentException if this node is not a descendant of the given node.
     */
    public Node<N> findDepthFirstRightNext(Predicate<N> predicate, Node<N> root) {
        for (Node<N> tmp = this; tmp != null; tmp = tmp.getDepthFirstRightNext(root)) {
            if (predicate.test(tmp.element)) {
                return tmp;
            }
        }
        return null;
    }

    /*
     * Utilities.
     */
    /**
     * Tells whether this node is equal to the given node.
     * <p/>
     * This function performs the following operations:
     * <ul>
     *     <li>Check whether the given object is an instance of class {@link Node}.</li>
     *     <li>Check whether this node is the same as the given object.</li>
     *     <li>Check whether the size of this node is equal to the size of the given node.</li>
     *     <li>Traverses both nodes simultaneously applying the preferred traversal algorithm for this node, and compare objects referenced by encountered nodes for equality.</li>
     * </ul>
     *
     * @param obj the node to be checked.
     * @return if this nodes is equal to the given object, false otherwise.
     * @throws IllegalArgumentException if the given object is not of type {@link Node}.
     */
    @Override
    @SuppressWarnings("unchecked")
    public boolean equals(Object obj) {
        if (!(obj instanceof Node)) {
            throw new IllegalArgumentException();
        }
        return Node.equals(this, (Node<N>) obj);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        int hash = Objects.hash(this.x, this.y, this.countAll, this.element);
        for (int i = 0; i < this.descendants.length; hash += 31 * hash + this.descendants[i++].hashCode()) ;
        return hash;
    }

    /**
     * Returns a shallow copy of this node.
     *
     * @return a shallow copy of this node
     */
    @Override
    @SuppressWarnings("unchecked")
    public Object clone() {
        try {
            Node<N> result = (Node<N>) super.clone();
            result.traversalAlgorithm = new ObjectReference<>(this.traversalAlgorithm.object);
            result.nextSibling = result.previousSibling = result.predecessor = null;
            result.descendants = new Node[0];
            result.x = result.y = 0;
            result.countAll = 1;
            for (int i = 0; i < this.descendants.length; result.add((Node<N>) this.descendants[i++].clone())) ;
            return result;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }

    /**
     * Returns a string representation of the (sub-)tree having this node as its root.
     *
     * @return a string representation of the (sub-)tree having this node as its root.
     */
    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        result.append("{ ");
        result.append("x: ").append(this.x).append(", ");
        result.append("y: ").append(this.y).append(", ");
        result.append("size: ").append(this.countAll).append(", ");
        result.append("element: ").append(this.element.toString().replaceAll("\\\\", "\\\\").replaceAll("\"", "\\\"")).append(", ");
        result.append("descendants: { ").append("size: ").append(this.descendants.length).append(", items: [ ");
        for (int i = 0; i < this.descendants.length; result.append(this.descendants[i].toString()).append(i == this.descendants.length - 1 ? " " : ", "), i++) ;
        result.append("] } }");
        return result.toString();
    }

    /**
     * See {@link Serializable}.
     */
    private void writeObject(ObjectOutputStream out) throws IOException {
        out.defaultWriteObject();
        out.writeObject(this.element);
        out.writeObject(this.traversalAlgorithm.object);
        out.writeInt(this.descendants.length);
        for (int i = 0; i < this.descendants.length; out.writeObject(this.descendants[i++])) ;
    }

    /**
     * See {@link Serializable}.
     */
    @SuppressWarnings("unchecked")
    private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        this.element = (N) in.readObject();
        this.countAll = 1;
        this.descendants = new Node[0];
        Object next = in.readObject();
        if (next instanceof TraversalAlgorithm) {
            this.traversalAlgorithm = new ObjectReference<>((TraversalAlgorithm) next);
            next = in.readInt();
        }
        for (int count = (int) next, i = 0; i < count; add((Node<N>) in.readObject()), i++) ;
    }

    /*
     * Node related data structures.
     */
    /**
     * An iterator that traverses a tree applying one of the algorithms supported by {@link Node}.
     * @see TraversalAlgorithm
     */
    public static class NodeIterator<N> implements Iterator<N> {
        /**
         * The root node of the tree to be traversed.
         */
        private Node<N> node;
        /**
         * Traversal algorithm of this iterator.
         */
        private TraversalAlgorithm ita;
        /**
         * Temporary placeholders for traversal, removal and verification.
         */
        private Node<?> next, previous;
        /**
         * A flag holding a boolean value indicating whether the node to be returned by {@link NodeIterator#next()} has been fetched from the tree.
         */
        private boolean isNext = false;
        /**
         * A flag holding a boolean value indicating whether a node has been removed.
         */
        private boolean removed = true;

        /**
         * Creates a node iterator given the root node and the traversal algorithm.
         *
         * @param node               the root node of the tree to be traversed.
         * @param traversalAlgorithm traversal algorithm.
         */
        public NodeIterator(Node<N> node, TraversalAlgorithm traversalAlgorithm) {
            this.node = node;
            this.ita = traversalAlgorithm;
        }

        @Override
        public boolean hasNext() {
            if (this.isNext) {
                return this.next != null;
            }
            this.isNext = true;
            this.advance();
            return this.next != null;
        }

        @Override
        @SuppressWarnings("unchecked")
        public N next() {
            this.removed = false;
            if (!this.isNext) {
                this.advance();
            }
            this.isNext = false;
            if (this.next == null) {
                throw new NoSuchElementException();
            }
            return (N) this.next.getElement();
        }

        @Override
        public void remove() {
            if (this.removed) {
                throw new IllegalStateException();
            }
            if (this.next == this.node) {
                this.advance();
            } else {
                this.removed = true;
                this.next.detach();
                this.next = this.previous;
                this.isNext = false;
            }
        }

        /**
         * Advances the current position of the iterator in the tree to the next node using the preferred traversal algorithm for the tree.
         */
        private void advance() {
            this.previous = this.next;
            this.next = (this.next == null) ? this.node : this.ita.getIterator().apply(this.next, this.node);
        }
    }

    /**
     * Enumerates the traversal algorithms supported by {@link Node}.
     */
    public enum TraversalAlgorithm {
        /**
         * Breadth-first left-to-right tree traversal algorithm constant value associated with the corresponding stepper function.
         */
        @SuppressWarnings("unchecked")
        BREADTH_FIRST_LEFT((e, f) -> e.getBreadthFirstLeftNext(f)),
        /**
         * Breadth-first right-to-left tree traversal algorithm constant value associated with the corresponding stepper function.
         */
        @SuppressWarnings("unchecked")
        BREADTH_FIRST_RIGHT((e, f) -> e.getBreadthFirstRightNext(f)),
        /**
         * Depth-first left-to-right tree traversal algorithm constant value associated with the corresponding stepper function.
         */
        @SuppressWarnings("unchecked")
        DEPTH_FIRST_LEFT((e, f) -> e.getDepthFirstLeftNext(f)),
        /**
         * Depth-first right-to-left tree traversal algorithm constant value associated with the corresponding stepper function.
         */
        @SuppressWarnings("unchecked")
        DEPTH_FIRST_RIGHT((e, f) -> e.getDepthFirstRightNext(f));
        /**
         * Stepper function placeholder.
         */
        @SuppressWarnings("rawtypes")
        private BiFunction<Node, Node, Node> iterate;

        /**
         * Creates a new {@link TraversalAlgorithm} constant value.
         *
         * @param iterate the stepper function.
         */
        @SuppressWarnings("rawtypes")
        TraversalAlgorithm(BiFunction<Node, Node, Node> iterate) {
            this.iterate = iterate;
        }

        /**
         * Gets the stepper function.
         *
         * @return the stepper function.
         */
        @SuppressWarnings("rawtypes")
        public BiFunction<Node, Node, Node> getIterator() {
            return this.iterate;
        }
    }

    /**
     * A helper class that serves as a pointer-to-pointer. An instance of this class will be shared among tree nodes, which makes it possible to change the preferred traversal algorithm for a tree from any node.
     *
     * @param <T> the type of the objects referenced by an instance of this class.
     */
    private static class ObjectReference<T> {
        /**
         * Referenced object
         */
        private T object;

        /**
         * Creates a new {@link ObjectReference} instance given an object to referenced.
         *
         * @param object the object referenced by this instance of {@link ObjectReference}.
         */
        public ObjectReference(T object) {
            this.object = object;
        }

        /**
         * Gets the referenced object.
         *
         * @return the object referenced by this instance of {@link ObjectReference}.
         */
        public T getObject() {
            return this.object;
        }

        /**
         * Sets the referenced object.
         *
         * @param object the object referenced by this instance of {@link ObjectReference}.
         */
        public void setObject(T object) {
            this.object = object;
        }
    }

    /*
     * Node logic.
     */
    /**
     * Translates a tree given its root node, a mapper function and the preferred traversal algorithm.
     *
     * @param node   root node of the tree to be translated.
     * @param mapper a function that translates elements from type <code><b>N</b></code> to type <code><b>M</b></code>.
     * @param <N>    type of elements of the source tree.
     * @param <M>    type of elements of the generated tree.
     * @return a tree that has the same structure as the tree having the given node as its root, referencing elements of type <code><b>M</b></code>.
     */
    public static <N, M> Node<M> translate(Node<N> node, Function<N, M> mapper) {
        return new Node<>(e -> e.descendants, node, e -> mapper.apply(e.element), node.traversalAlgorithm.object);
    }

    /**
     * A function that compares two trees given two root nodes for equality.
     *
     * @param node1      left-hand operand.
     * @param node2      right-hand operand.
     * @param comparator a function that compares two elements, one from each tree, for equality.
     * @param <N>        type of objects referenced by nodes of both trees.
     * @return true if both trees are equal, false otherwise.
     */
    public static <N> boolean equals(Node<N> node1, Node<N> node2, Comparator<N> comparator) {
        return Node.equals(node1, node2, (BiPredicate<N, N>) (e, f) -> comparator.compare(e, f) == 0);
    }

    /**
     * A function that compares two trees given two root nodes for equality.
     * <p/>
     * Equality of two elements is evaluated using {@link Objects#equals(Object, Object)}.
     *
     * @param node1 left-hand operand.
     * @param node2 right-hand operand.
     * @param <N>   type of objects referenced by nodes of both trees.
     * @return true if both trees are equal, false otherwise.
     */
    public static <N> boolean equals(Node<N> node1, Node<N> node2) {
        return Node.equals(node1, node2, (BiPredicate<N, N>) (e, f) -> Objects.equals(e, f));
    }

    /**
     * A function that compares two trees given two root nodes for equality.
     *
     * @param node1     left-hand operand.
     * @param node2     right-hand operand.
     * @param predicate a function that evaluates the equality of two nodes one from each tree.
     * @param <N>       type of objects referenced by nodes of both trees.
     * @return true if both trees are equal, false otherwise.
     */
    public static <N> boolean equals(Node<N> node1, Node<N> node2, BiPredicate<N, N> predicate) {
        return Node.equals(node1, predicate, node2);
    }

    /**
     * A function that compares two trees given two root nodes for equality.
     *
     * @param node1     left-hand operand.
     * @param predicate a function that evaluates equality of two nodes one from each tree.
     * @param node2     right-hand operand.
     * @param <N>       type of objects referenced by nodes of the first tree.
     * @param <M>       type of objects referenced by nodes of the second tree.
     * @return true if both trees are equal, false otherwise.
     */
    @SuppressWarnings("unchecked")
    public static <N, M> boolean equals(Node<N> node1, BiPredicate<N, M> predicate, Node<M> node2) {
        if (node1 == node2) {
            return true;
        }
        if (node1 == null ^ node2 == null) {
            return false;
        }
        if (node1.countAll != node2.countAll) {
            return false;
        }
        TraversalAlgorithm preferredTraversalAlgorithm = node1.traversalAlgorithm.object == TraversalAlgorithm.DEPTH_FIRST_LEFT || node1.traversalAlgorithm.object == TraversalAlgorithm.BREADTH_FIRST_LEFT ? TraversalAlgorithm.DEPTH_FIRST_LEFT : TraversalAlgorithm.DEPTH_FIRST_RIGHT;
        Node<N> tmp1;
        Node<M> tmp2;
        for (tmp1 = node1, tmp2 = node2; tmp1 != null ; tmp1 = (Node<N>) preferredTraversalAlgorithm.iterate.apply(tmp1, tmp1), tmp2 = (Node<M>) preferredTraversalAlgorithm.iterate.apply(tmp2, tmp2)) {
            if (!predicate.test(tmp1.element, tmp2.element)) {
                return false;
            }
        }
        return true;
    }
}