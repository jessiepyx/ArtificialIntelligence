# coding=utf-8
from engines import Engine
from random import shuffle
import sys
import math
import random
import copy

FULL_MASK = 0xFFFFFFFFFFFFFFFF
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


def get_lsb(bitmap):  # 返回的是bitmap最后一个1的**位置**
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
    return [W, B]


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


def get_move_list(bit_move):
    move_list = []
    while bit_move != 0:
        move, bit_move = pop_lsb(bit_move)
        move_list.append(move)
    return move_list


def to_move(oct_move):
    # print("oct_move: %d" % oct_move)
    return oct_move % 8, oct_move // 8  # (x,y)

# todo: 这以上都不用检查了


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
            # print("best:")
            # print(self.visited_times)
            # print(child.visited_times)
            second = 2.0 * math.log(self.visited_times) / child.visited_times
            score = first + C * math.sqrt(second)
            if score > best_score:
                best_child = child
                best_score = score
        return best_child

    def expand(self):
        # print("expand:0x%x, 0x%x" % (self.state.current_board))
        (curW, curB) = self.state.current_board  # 获得当前棋盘状态
        random_move = None
        if len(self.state.available_moves) != 0:
            random_move = self.state.available_moves[self.state.current_step]  # available_moves存储了所有的可行解
            self.state.current_step += 1  # 移动到下一个move
            flip_mask = flip(curW, curB, random_move)  # 计算当前的move会引起的翻转情况
            curW ^= (flip_mask | BIT[random_move])  # 该部分被翻转，并且添加上随机走的子
            curB ^= flip_mask  # 该部分被翻转
        child_node = Node()  # 生成新的子节点
        new_state = State()  # 生成新的State
        new_state.color = self.state.color * -1  # 更新新的State的Color数据
        new_state.current_board = (curB, curW)  # 更新新的State的棋盘数据
        next_moves = move_gen(curB, curW)  # 生成可行解的移动序
        new_state.available_moves = get_move_list(next_moves)
        shuffle(new_state.available_moves)  # 随机安排move的顺序
        new_state.move_from_parent = random_move  # 安排子节点是由父节点的哪个move移动过来的
        child_node.parent = self
        child_node.state = new_state  # 安排子节点的State为新生成的State
        self.children.append(child_node)  # 把当前新建的节点append到父节点的子节点序列中
        return child_node


class State:
    def __init__(self):
        self.color = 1  # 1: 白棋， -1：黑棋
        self.available_moves = []  # 可行移动操作序列
        self.current_step = 0  # 当前已经尝试过哪些可行移动操作序列
        self.current_board = (None, None)  # (My, Opponent's)两个局面
        self.move_from_parent = 0  # 通过父节点的哪个move移动过来的，这里保存的是move的十进制数字编码

    '''
    . 1 . . . . 1 .    . . . . . . . .    . . 1 . . 1 . .    . . . . . . . .
    1 . . . . . . 1    . 1 . . . . 1 .    . . . . . . . .    . . 1 . . 1 . .
    . . . . . . . .    . . . . . . . .    1 . . . . . . 1    . 1 . . . . 1 .
    . . . 1 1 . . .    . . . . . . . .    . . . . . . . .    . . . . . . . .
    . . . 1 1 . . .    . . . . . . . .    . . . . . . . .    . . . . . . . .
    . . . . . . . .    . . . . . . . .    1 . . . . . . 1    . 1 . . . . 1 .
    1 . . . . . . 1    . 1 . . . . 1 .    . . . . . . . .    . . 1 . . 1 . .
    . 1 . . . . 1 .    . . . . . . . .    . . 1 . . 1 . .    . . . . . . . .
    
          -3                 -7                  11                -4
          
    . . . 1 1 . . .    . . . . . . . .    . . . . . . . .
    . . . . . . . .    . . . 1 1 . . .    . . . . . . . .
    . . . . . . . .    . . . . . . . .    . . 1 1 1 1 . .
    1 . . . . . . 1    . 1 . . . . 1 .    . . 1 . . 1 . .
    1 . . . . . . 1    . 1 . . . . 1 .    . . 1 . . 1 . .
    . . . . . . . .    . . . . . . . .    . . 1 1 1 1 . .
    . . . . . . . .    . . . 1 1 . . .    . . . . . . . .
    . . . 1 1 . . .    . . . . . . . .    . . . . . . . .
    
           8                  1                  2
    '''
    WEIGHTS = \
        [-3, -7, 11, -4, 8, 1, 2]
    P_RINGS = [0x4281001818008142,
               0x42000000004200,
               0x2400810000810024,
               0x24420000422400,
               0x1800008181000018,
               0x18004242001800,
               0x3C24243C0000]
    P_CORNER = 0x8100000000000081
    P_SUB_CORNER = 0x42C300000000C342

    def compute_reward(self, root_color, current_color):
        W = self.current_board[0]
        B = self.current_board[1]

        mycorner = bit_count(W & self.P_CORNER)
        opcorner = bit_count(B & self.P_CORNER)

        # piece difference
        mypiece = mycorner * 100
        for i in range(len(self.WEIGHTS)):
            mypiece += self.WEIGHTS[i] * bit_count(W & self.P_RINGS[i])
        oppiece = opcorner * 100
        for i in range(len(self.WEIGHTS)):
            oppiece += self.WEIGHTS[i] * bit_count(B & self.P_RINGS[i])

        # scorepiece = \
        #             10.0 * mypiece / (mypiece + oppiece) if mypiece > oppiece \
        #             else -10.0 * oppiece / (mypiece + oppiece) if mypiece < oppiece \
        #             else 0
        scorepiece = mypiece - oppiece

        return scorepiece * root_color * current_color
        # 这里计算出的代价是白色方的收益，如果当前颜色和root颜色相同，则说明当前执白

    def terminal(self):
        first_bitmove = move_gen(self.current_board[0], self.current_board[1])
        second_bitmove = move_gen(self.current_board[1], self.current_board[0])
       ## # print(first_bitmove)
       # # print(second_bitmove)
        return (first_bitmove == 0) & (second_bitmove == 0)

    def get_next_move_with_random_choice(self):
        # print(self.color)
        if len(self.available_moves) == 0:
            self.color = self.color * -1  # 更新新的State的Color数据
            (curW, curB) = self.current_board  # 获得当前棋盘状态
            self.current_board = (curB, curW)  # 更新新的State的棋盘数据
            next_moves = move_gen(curB, curW)  # 生成可行解的移动序列
            self.available_moves = get_move_list(next_moves)
            shuffle(self.available_moves)  # 随机安排move的顺序
            return
        # # print("move:0x%x, 0x%x"%(self.current_board))
        # # print(self.available_moves)
        shuffle(self.available_moves)
        random_move = self.available_moves[0]
        (curW, curB) = self.current_board  # 获得当前棋盘状态
        flip_mask = flip(curW, curB, random_move)  # 计算当前的move会引起的翻转情况
        curW ^= flip_mask | BIT[random_move]  # 该部分被翻转，并且添加上随机走的子
        curB ^= flip_mask  # 该部分被翻转
        self.color = self.color * -1  # 更新新的State的Color数据
        self.current_board = (curB, curW)  # 更新新的State的棋盘数据
        next_moves = move_gen(curB, curW)  # 生成可行解的移动序列
        self.available_moves = get_move_list(next_moves)
        shuffle(self.available_moves)  # 随机安排move的顺序


class MonteCarloTree:
    def __init__(self):
        self.budget = 200  # 计算资源的预算
        self.root = Node()  # 根节点
        new_state = State()  # 根节点的状态
        self.root.state = new_state  # 绑定状态与节点

    def init_tree(self, board, color):
        self.root.state.current_board = to_bitboard(board)  # 将board数据转化成位图数据
        # 这里默认root对应的board中，我方执白
        self.root.state.available_moves = get_move_list(move_gen(self.root.state.current_board[0],
                                                                 self.root.state.current_board[1]))
        shuffle(self.root.state.available_moves)
        # 生成根节点的所有可行移动
        self.root.state.color = color  # 标记当前颜色

    @staticmethod
    def tree_policy(node):
        while not node.state.terminal():  # 只要当前局面未陷入终止状态，则继续采用Tree_policy
            if node.all_expanded() and len(node.state.available_moves) != 0:  # 如果全部展开了，就再向下寻找最优子节点
                node = node.best_child(True)
            else:
                child = node.expand()  # 如果还有没展开的就展开出一个新的节点
                return child  # Tree_Policy展开获得了当前的节点
        return node

    def default_policy(self, node):
        current_state = copy.deepcopy(node.state)
        while not current_state.terminal():
            current_state.get_next_move_with_random_choice()
        final_state_reward = current_state.compute_reward(self.root.state.color, current_state.color)
        return final_state_reward

    def backup(self, node, reward):
        while node is not None:
            node.visited_times += 1
            node.quality_value += reward
            node = node.parent

    def tree_search(self, node):
        for _ in range(self.budget):
            # 1. 寻找最优节点进行展开
            expand_node = self.tree_policy(node)
            # 2. 随机运行并计算结果
            reward = self.default_policy(expand_node)
            # print("reward:%d"%reward)
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
        mcTree = MonteCarloTree()
        mcTree.init_tree(board, color)
        if mcTree.tree_search(mcTree.root) is None:
            return None
        else:
            return to_move(mcTree.tree_search(mcTree.root).state.move_from_parent)


engine = DesmondEngine