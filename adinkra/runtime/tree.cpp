#include <__adinkra/tree>

_ADINKRA_BEGIN_NAMESPACE_STD

namespace __tree {

namespace {

bool is_red(const node_base* node) noexcept {
    return node != nullptr && node->red;
}

bool is_black(const node_base* node) noexcept {
    return !is_red(node);
}

void rotate_left(node_base*& root, node_base* node) noexcept {
    node_base* pivot = node->right;
    node->right = pivot->left;
    if (pivot->left != nullptr) {
        pivot->left->parent = node;
    }
    pivot->parent = node->parent;
    if (node->parent == nullptr) {
        root = pivot;
    } else if (node == node->parent->left) {
        node->parent->left = pivot;
    } else {
        node->parent->right = pivot;
    }
    pivot->left = node;
    node->parent = pivot;
}

void rotate_right(node_base*& root, node_base* node) noexcept {
    node_base* pivot = node->left;
    node->left = pivot->right;
    if (pivot->right != nullptr) {
        pivot->right->parent = node;
    }
    pivot->parent = node->parent;
    if (node->parent == nullptr) {
        root = pivot;
    } else if (node == node->parent->right) {
        node->parent->right = pivot;
    } else {
        node->parent->left = pivot;
    }
    pivot->right = node;
    node->parent = pivot;
}

void transplant(
    node_base*& root, node_base* removed,
    node_base* replacement) noexcept {
    if (removed->parent == nullptr) {
        root = replacement;
    } else if (removed == removed->parent->left) {
        removed->parent->left = replacement;
    } else {
        removed->parent->right = replacement;
    }
    if (replacement != nullptr) {
        replacement->parent = removed->parent;
    }
}

void erase_fix(
    node_base*& root, node_base* node,
    node_base* parent) noexcept {
    while (node != root && is_black(node)) {
        if (parent == nullptr) {
            break;
        }
        if (node == parent->left) {
            node_base* sibling = parent->right;
            if (is_red(sibling)) {
                sibling->red = false;
                parent->red = true;
                rotate_left(root, parent);
                sibling = parent->right;
            }
            if (sibling == nullptr) {
                node = parent;
                parent = node->parent;
                continue;
            }
            if (is_black(sibling->left) &&
                is_black(sibling->right)) {
                sibling->red = true;
                node = parent;
                parent = node->parent;
            } else {
                if (is_black(sibling->right)) {
                    if (sibling->left != nullptr) {
                        sibling->left->red = false;
                    }
                    sibling->red = true;
                    rotate_right(root, sibling);
                    sibling = parent->right;
                }
                sibling->red = parent->red;
                parent->red = false;
                if (sibling->right != nullptr) {
                    sibling->right->red = false;
                }
                rotate_left(root, parent);
                node = root;
                parent = nullptr;
            }
        } else {
            node_base* sibling = parent->left;
            if (is_red(sibling)) {
                sibling->red = false;
                parent->red = true;
                rotate_right(root, parent);
                sibling = parent->left;
            }
            if (sibling == nullptr) {
                node = parent;
                parent = node->parent;
                continue;
            }
            if (is_black(sibling->left) &&
                is_black(sibling->right)) {
                sibling->red = true;
                node = parent;
                parent = node->parent;
            } else {
                if (is_black(sibling->left)) {
                    if (sibling->right != nullptr) {
                        sibling->right->red = false;
                    }
                    sibling->red = true;
                    rotate_left(root, sibling);
                    sibling = parent->left;
                }
                sibling->red = parent->red;
                parent->red = false;
                if (sibling->left != nullptr) {
                    sibling->left->red = false;
                }
                rotate_right(root, parent);
                node = root;
                parent = nullptr;
            }
        }
    }
    if (node != nullptr) {
        node->red = false;
    }
}

} // namespace

node_base* minimum(node_base* node) noexcept {
    if (node == nullptr) {
        return nullptr;
    }
    while (node->left != nullptr) {
        node = node->left;
    }
    return node;
}

const node_base* minimum(const node_base* node) noexcept {
    return minimum(const_cast<node_base*>(node));
}

node_base* maximum(node_base* node) noexcept {
    if (node == nullptr) {
        return nullptr;
    }
    while (node->right != nullptr) {
        node = node->right;
    }
    return node;
}

const node_base* maximum(const node_base* node) noexcept {
    return maximum(const_cast<node_base*>(node));
}

node_base* next(node_base* node) noexcept {
    if (node->right != nullptr) {
        return minimum(node->right);
    }
    node_base* parent = node->parent;
    while (parent != nullptr && node == parent->right) {
        node = parent;
        parent = parent->parent;
    }
    return parent;
}

const node_base* next(const node_base* node) noexcept {
    return next(const_cast<node_base*>(node));
}

node_base* previous(node_base* node) noexcept {
    if (node->left != nullptr) {
        return maximum(node->left);
    }
    node_base* parent = node->parent;
    while (parent != nullptr && node == parent->left) {
        node = parent;
        parent = parent->parent;
    }
    return parent;
}

const node_base* previous(const node_base* node) noexcept {
    return previous(const_cast<node_base*>(node));
}

void insert_rebalance(
    node_base*& root, node_base* node) noexcept {
    node->left = nullptr;
    node->right = nullptr;
    node->red = true;

    while (node != root && is_red(node->parent)) {
        node_base* parent = node->parent;
        node_base* grandparent = parent->parent;
        if (parent == grandparent->left) {
            node_base* uncle = grandparent->right;
            if (is_red(uncle)) {
                parent->red = false;
                uncle->red = false;
                grandparent->red = true;
                node = grandparent;
            } else {
                if (node == parent->right) {
                    node = parent;
                    rotate_left(root, node);
                    parent = node->parent;
                    grandparent = parent->parent;
                }
                parent->red = false;
                grandparent->red = true;
                rotate_right(root, grandparent);
            }
        } else {
            node_base* uncle = grandparent->left;
            if (is_red(uncle)) {
                parent->red = false;
                uncle->red = false;
                grandparent->red = true;
                node = grandparent;
            } else {
                if (node == parent->left) {
                    node = parent;
                    rotate_right(root, node);
                    parent = node->parent;
                    grandparent = parent->parent;
                }
                parent->red = false;
                grandparent->red = true;
                rotate_left(root, grandparent);
            }
        }
    }
    root->red = false;
}

void erase_rebalance(
    node_base*& root, node_base* removed) noexcept {
    node_base* moved = removed;
    bool moved_was_red = moved->red;
    node_base* replacement = nullptr;
    node_base* replacement_parent = nullptr;

    if (removed->left == nullptr) {
        replacement = removed->right;
        replacement_parent = removed->parent;
        transplant(root, removed, removed->right);
    } else if (removed->right == nullptr) {
        replacement = removed->left;
        replacement_parent = removed->parent;
        transplant(root, removed, removed->left);
    } else {
        moved = minimum(removed->right);
        moved_was_red = moved->red;
        replacement = moved->right;
        if (moved->parent == removed) {
            replacement_parent = moved;
            if (replacement != nullptr) {
                replacement->parent = moved;
            }
        } else {
            replacement_parent = moved->parent;
            transplant(root, moved, moved->right);
            moved->right = removed->right;
            moved->right->parent = moved;
        }
        transplant(root, removed, moved);
        moved->left = removed->left;
        moved->left->parent = moved;
        moved->red = removed->red;
    }

    if (!moved_was_red) {
        erase_fix(root, replacement, replacement_parent);
    }
}

} // namespace __tree

_ADINKRA_END_NAMESPACE_STD
