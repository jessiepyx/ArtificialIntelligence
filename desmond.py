from engines import Engine
from random import shuffle
import sys
import math

FULL_MASK = 0xFFFFFFFF
RADIAL_MAP = {}
RADIAL_BASE = {-1: (-1, 0), 1: (1, 0), -8: (0, -1), 8: (0, 1), -7: (1, -1), 7: (-1, 1), -9: (-1, -1), 9: (1, 1)}
DIR = [
    [1, -7, -8],
    [-1, -9, -8],
    [1, 8, 9],
    [7, 8, -1],
    [8, 9, 1, -7, -8],
    [-1, 1, -7, -8, -9],
    [7, 8, -1, -9, -8],
    [7, 8, 9, -1, 1],
    [-1, 1, -7, 7, -8, 8, -9, 9]]

SQ_DIR = \
    [2, 2, 7, 7, 7, 7, 3, 3,
     2, 2, 7, 7, 7, 7, 3, 3,
     4, 4, 8, 8, 8, 8, 6, 6,
     4, 4, 8, 8, 8, 8, 6, 6,
     4, 4, 8, 8, 8, 8, 6, 6,
     4, 4, 8, 8, 8, 8, 6, 6,
     0, 0, 5, 5, 5, 5, 1, 1,
     0, 0, 5, 5, 5, 5, 1, 1]


def fill_radial_map():
    for dir, dir_mv in list(RADIAL_BASE.items()):
        lis = [0] * 64
        for sqr in range(64):
            mask = 0
            sq = sqr
            x, y = to_move(sq)
            sq += dir
            x += dir_mv[0]
            y += dir_mv[1]
            while 0 <= x < 8 and 0 <= y < 8 and 0 <= sq < 64:
                mask |= BIT[sq]
                sq += dir
                x += dir_mv[0]
                y += dir_mv[1]
            lis[sqr] = mask
        RADIAL_MAP[dir] = lis


def flip(W, B, mv):
    mask = 0
    for dir in DIR[SQ_DIR[mv]]:
        mvtmp = mv
        mvtmp += dir
        while 0 <= mvtmp < 64 and (BIT[mvtmp] & B != 0) and (BIT[mvtmp] & RADIAL_MAP[dir][mv] != 0):
            mvtmp += dir
        if 0 <= mvtmp < 64 and (BIT[mvtmp] & W != 0) and (BIT[mvtmp] & RADIAL_MAP[dir][mv] != 0):
            mvtmp -= dir
            while mvtmp != mv:
                mask |= BIT[mvtmp]
                mvtmp -= dir
    return mask


def bit_count(b):
    b = (b & 0x5555555555555555) + (b >> 1 & 0x5555555555555555)
    b = (b & 0x3333333333333333) + (b >> 2 & 0x3333333333333333)
    b = b + (b >> 4) & 0x0F0F0F0F0F0F0F0F
    b = b + (b >> 8)
    b = b + (b >> 16)
    b = b + (b >> 32) & 0x0000007F
    return b


def get_lsb(bitmap):
    ans = 0
    curMask = 0xFFFFFFFF
    curLen = 32
    val = bitmap & (~(bitmap & (bitmap - 1)) & FULL_MASK)
    while not (curLen == 0):
        if val & curMask == 0:
            ans += curLen
            val >>= curLen
        curLen >>= 1
        curMask >>= curLen
    return ans

def pop_lsb(bitmap):
    return get_lsb(bitmap), bitmap & (bitmap - 1)

def fill_bit_table():
    global BIT
    BIT = [1 << n for n in range(64)]


def to_bitboard(board):
    W = 0
    B = 0
    for r in range(8):
        for c in range(8):
            if board[c][r] == -1:
                B |= BIT[8 * r + c]
            elif board[c][r] == 1:
                W |= BIT[8 * r + c]
    return W, B


def move_gen_sub(P, mask, dir):
    # 先算从P向dir出发的全体连续的mask在哪些位置上
    dir2 = int(dir * 2)
    flip1 = mask & (P << dir)  # 当前棋盘向指定方向移动的结果与mask重合的部分
    flip2 = mask & (P >> dir)  # 当前棋盘向指定的另一方向移动的结果与mask重合的部分
    flip1 |= mask & (flip1 << dir)  # 当前棋盘沿着dir方向前进一步或连续两步后的重合的部分
    flip2 |= mask & (flip2 >> dir)  # 同理
    mask1 = mask & (mask << dir)  # mask沿当前方向移动一次与原mask重合的部分，求得沿当前方向连续两个mask棋子都在的情况
    mask2 = mask & (mask >> dir)
    flip1 |= mask1 & (flip1 << dir2)  # 连续走两步和mask重合的部分 再 走两步，这两步中与上一个更新的mask重合的部分（连续3/4个mask棋子）
    flip2 |= mask2 & (flip2 >> dir2)
    flip1 |= mask1 & (flip1 << dir2)  # 连续5/6个mask棋子
    flip2 |= mask2 & (flip2 >> dir2)
    return (flip1 << dir) | (flip2 >> dir)  # 算1-6就够了，因为要算上当前player的下子的两个端位


def move_gen(M, O):
    # 生成我的合法下子位置
    mask = O & 0x7E7E7E7E7E7E7E7E  # mask是O去掉左右两列的结果
    return ((move_gen_sub(M, mask, 1) \
             | move_gen_sub(M, O, 8) \
             | move_gen_sub(M, mask, 7) \
             | move_gen_sub(M, mask, 9)) & ~(M | O)) & FULL_MASK  # 弃掉两端是因为两端移动一位以后结果不正确。
    # 去掉已经被占据的格子
    # << 1 : 所有格子向左移动一位，>> 1 : 所有格子向右移动一位
    # << 8 : 上移一位， >> 8 : 下移一位
    # << 7 ：右上， >> 7 : 左下
    # << 9 ：左上， >> 9 : 右下


def get_move_list(next_moves):
    move_list = []
    while next_moves != 0:
        move, next_moves = pop_lsb(next_moves)
        move_list.append(move)
    return move_list


def to_move(bitmove):
    return bitmove % 8, bitmove // 8  # (x,y)


def to_bitmove(move):
    return move[0] + 8 * move[1]


class Node:
    def __init__(self):
        self.parent = None
        self.children = []
        self.visited_times = 0
        self.state = None
        self.quality_value = 0.0

    def all_expanded(self):
        return self.state.current_step >= len(self.state.available_moves)

    def best_child(self, is_exploration):
        best_score = -sys.maxsize
        best_child = None
        # UCB算法
        for child in self.children:
            if is_exploration:
                C = 1 / math.sqrt(2.0)
            else:
                C = 0.0
            first = child.quality_value / child.visited_times
            second = 2.0 * math.log(self.visited_times) / child.visited_times
            score = first + C * second
            if score > best_score:
                best_child = child
        return best_child

    def expand(self):
        random_move = self.state.available_moves[self.state.current_step]  # available_moves存储了所有的可行解
        self.state.current_step += 1                                       # 移动到下一个move
        (curW, curB) = self.state.current_board
        flip_mask = flip(curW, curB, random_move)
        curW ^= flip_mask | BIT[random_move]    # 该部分被翻转，并且添加上随机走的子
        curB ^= flip_mask                       # 该部分被翻转
        child_node = Node()
        new_state = State()
        new_state.color = self.state.color * -1
        new_state.current_board = (curB, curW)
        next_moves = move_gen(curB, curW)
        new_state.available_moves = shuffle(get_move_list(next_moves))  # 随机安排move的顺序
        new_state.current_step = 0
        child_node.state = new_state
        self.children.append(child_node)
        return child_node


class State:
    def __init__(self):
        self.color = 1  # 1: 白棋， -1：黑棋
        self.value = 0.0
        self.terminal = False
        self.available_moves = []
        self.current_step = 0
        self.current_board = (None, None)  # (My, Opponent's)两个局面


class MonteCarloTree:
    def __init__(self):
        self.budget = 1000
        self.root = Node()
        new_state = State()
        self.root.state = new_state

    def init_tree(self, board, color):
        self.root.state.current_board = to_bitboard(board)
        self.root.state.available_moves = get_move_list(move_gen(self.root.state.current_board[0], self.root.state.current_board[1]))
        self.root.state.color = color

    @staticmethod
    def tree_policy(node):
        while not node.state.terminal:
            if node.all_expanded():
                node = node.best_child(True)
            else:
                child = node.expand()
                return child
        return node

    def default_policy(self, node):
        pass

    def backup(self, node, reward):
        pass

    def tree_search(self, node):
        for i in range(self.budget):
            # 1. 寻找最优节点进行展开
            expand_node = self.tree_policy(node)
            # 2. 随机运行并计算结果
            reward = self.default_policy(expand_node)
            # 3. 更新所有路径上的节点
            self.backup(expand_node, reward)
        best_child = node.best_child(False)
        return best_child


class DesmondEngine(Engine):
    def __init__(self):
        fill_bit_table()
        fill_radial_map()

    def get_move(self, board, color, move_num=None,
                 time_remaining=None, time_opponent=None):
        moves = board.get_legal_moves(color)
        pass
