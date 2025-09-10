#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <sstream>
#include <map>
#include <algorithm>
#include <stdexcept>
#include <limits>
#include <cstdint> 
#include <chrono>  

#ifdef _MSC_VER
#include <intrin.h> 
#endif


const int INF = 100000;
const double BLUNDER_THRESHOLD = 200.0;
const double INACCURACY_THRESHOLD = 80.0;


using U64 = uint64_t;

enum Square {
    A1, B1, C1, D1, E1, F1, G1, H1,
    A2, B2, C2, D2, E2, F2, G2, H2,
    A3, B3, C3, D3, E3, F3, G3, H3,
    A4, B4, C4, D4, E4, F4, G4, H4,
    A5, B5, C5, D5, E5, F5, G5, H5,
    A6, B6, C6, D6, E6, F6, G6, H6,
    A7, B7, C7, D7, E7, F7, G7, H7,
    A8, B8, C8, D8, E8, F8, G8, H8, NO_SQ
};

enum Piece { P, N, B, R, Q, K, p, n, b, r, q, k, NO_PIECE };
enum Color { WHITE, BLACK, BOTH };
enum CastlingRights { WK = 1, WQ = 2, BK = 4, BQ = 8 };


inline void set_bit(U64 &bb, int square) { bb |= (1ULL << square); }
inline bool get_bit(U64 bb, int square) { return (bb >> square) & 1; }
inline void pop_bit(U64 &bb, int square) { bb &= ~(1ULL << square); }
inline int lsb_index(U64 bb) {
    if (bb == 0) return -1;
    #ifdef _MSC_VER
        unsigned long index;
        _BitScanForward64(&index, bb);
        return index;
    #else
        return __builtin_ctzll(bb);
    #endif
}

const U64 not_a_file = 18374403900871474942ULL;
const U64 not_h_file = 9187201950435737471ULL;
const U64 not_hg_file = 4557430888798830399ULL;
const U64 not_ab_file = 18229723555195321596ULL;


U64 pawn_attacks[2][64];
U64 knight_attacks[64];
U64 king_attacks[64];

U64 get_bishop_attacks(int sq, U64 occupancy) {
    U64 attacks = 0ULL;
    int r, f;
    int tr = sq / 8;
    int tf = sq % 8;
    for (r = tr + 1, f = tf + 1; r <= 7 && f <= 7; r++, f++) { attacks |= (1ULL << (r * 8 + f)); if ((1ULL << (r * 8 + f)) & occupancy) break; }
    for (r = tr + 1, f = tf - 1; r <= 7 && f >= 0; r++, f--) { attacks |= (1ULL << (r * 8 + f)); if ((1ULL << (r * 8 + f)) & occupancy) break; }
    for (r = tr - 1, f = tf + 1; r >= 0 && f <= 7; r--, f++) { attacks |= (1ULL << (r * 8 + f)); if ((1ULL << (r * 8 + f)) & occupancy) break; }
    for (r = tr - 1, f = tf - 1; r >= 0 && f >= 0; r--, f--) { attacks |= (1ULL << (r * 8 + f)); if ((1ULL << (r * 8 + f)) & occupancy) break; }
    return attacks;
}

U64 get_rook_attacks(int sq, U64 occupancy) {
    U64 attacks = 0ULL;
    int r, f;
    int tr = sq / 8;
    int tf = sq % 8;
    for (r = tr + 1; r <= 7; r++) { attacks |= (1ULL << (r * 8 + tf)); if ((1ULL << (r * 8 + tf)) & occupancy) break; }
    for (r = tr - 1; r >= 0; r--) { attacks |= (1ULL << (r * 8 + tf)); if ((1ULL << (r * 8 + tf)) & occupancy) break; }
    for (f = tf + 1; f <= 7; f++) { attacks |= (1ULL << (tr * 8 + f)); if ((1ULL << (tr * 8 + f)) & occupancy) break; }
    for (f = tf - 1; f >= 0; f--) { attacks |= (1ULL << (tr * 8 + f)); if ((1ULL << (tr * 8 + f)) & occupancy) break; }
    return attacks;
}

void initialize_leaper_attacks() {
    for (int sq = 0; sq < 64; sq++) {
        pawn_attacks[WHITE][sq] = 0ULL; pawn_attacks[BLACK][sq] = 0ULL;
        knight_attacks[sq] = 0ULL; king_attacks[sq] = 0ULL;
    }
    for (int sq = 0; sq < 64; sq++) {
        U64 bit = 1ULL << sq;
        
        if ((bit << 7) & not_h_file) pawn_attacks[WHITE][sq] |= (bit << 7);
        if ((bit << 9) & not_a_file) pawn_attacks[WHITE][sq] |= (bit << 9);
        
        if ((bit >> 7) & not_a_file) pawn_attacks[BLACK][sq] |= (bit >> 7);
        if ((bit >> 9) & not_h_file) pawn_attacks[BLACK][sq] |= (bit >> 9);
        
        if ((bit << 17) & not_a_file) knight_attacks[sq] |= (bit << 17);
        if ((bit << 15) & not_h_file) knight_attacks[sq] |= (bit << 15);
        if ((bit << 10) & not_ab_file) knight_attacks[sq] |= (bit << 10);
        if ((bit << 6) & not_hg_file) knight_attacks[sq] |= (bit << 6);
        if ((bit >> 17) & not_h_file) knight_attacks[sq] |= (bit >> 17);
        if ((bit >> 15) & not_a_file) knight_attacks[sq] |= (bit >> 15);
        if ((bit >> 10) & not_hg_file) knight_attacks[sq] |= (bit >> 10);
        if ((bit >> 6) & not_ab_file) knight_attacks[sq] |= (bit >> 6);
        U64 k_attacks = 0ULL;
        if ((bit << 8)) k_attacks |= (bit << 8);
        if ((bit << 9) & not_a_file) k_attacks |= (bit << 9);
        if ((bit << 7) & not_h_file) k_attacks |= (bit << 7);
        if ((bit << 1) & not_a_file) k_attacks |= (bit << 1);
        if ((bit >> 8)) k_attacks |= (bit >> 8);
        if ((bit >> 9) & not_h_file) k_attacks |= (bit >> 9);
        if ((bit >> 7) & not_a_file) k_attacks |= (bit >> 7);
        if ((bit >> 1) & not_h_file) k_attacks |= (bit >> 1);
        king_attacks[sq] = k_attacks;
    }
}



struct Move {
    int from_sq;
    int to_sq;
    int piece;
    int promotion = NO_PIECE;
    int captured_piece = NO_PIECE;
    int double_push = 0;
    int enpassant = 0;
    int castling = 0;

    std::string toString() const {
        std::string s = "";
        s += (char)('a' + (from_sq % 8));
        s += std::to_string(1 + (from_sq / 8));
        s += (char)('a' + (to_sq % 8));
        s += std::to_string(1 + (to_sq / 8));
        if (promotion != NO_PIECE) {
            char promo_char = ' ';
            switch(promotion) {
                case Q: promo_char = 'q'; break; case R: promo_char = 'r'; break;
                case B: promo_char = 'b'; break; case N: promo_char = 'n'; break;
                default: break;
            }
            if(promo_char != ' ') s += promo_char;
        }
        return s;
    }
};


const int piece_values[] = { 100, 320, 330, 500, 900, 20000 };
const int pawn_table[64] = {0,0,0,0,0,0,0,0,50,50,50,50,50,50,50,50,10,10,20,30,30,20,10,10,5,5,10,25,25,10,5,5,0,0,0,20,20,0,0,0,5,-5,-10,0,0,-10,-5,5,5,10,10,-20,-20,10,10,5,0,0,0,0,0,0,0,0};
const int knight_table[64] = {-50,-40,-30,-30,-30,-30,-40,-50,-40,-20,0,0,0,0,-20,-40,-30,0,10,15,15,10,0,-30,-30,5,15,20,20,15,5,-30,-30,0,15,20,20,15,0,-30,-30,5,10,15,15,10,5,-30,-40,-20,0,5,5,0,-20,-40,-50,-40,-30,-30,-30,-30,-40,-50};
const int bishop_table[64] = {-20,-10,-10,-10,-10,-10,-10,-20,-10,0,0,0,0,0,0,-10,-10,0,5,10,10,5,0,-10,-10,5,5,10,10,5,5,-10,-10,0,10,10,10,10,0,-10,-10,10,10,10,10,10,10,-10,-10,5,0,0,0,0,5,-10,-20,-10,-10,-10,-10,-10,-10,-20};
const int rook_table[64] = {0,0,0,0,0,0,0,0,5,10,10,10,10,10,10,5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,0,0,0,5,5,0,0,0};
const int king_table[64] = {-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-20,-30,-30,-40,-40,-30,-30,-20,-10,-20,-20,-20,-20,-20,-10,-20,20,20,0,0,0,0,20,20,20,30,10,0,0,10,30,20};
const int king_table_end_game[64] = {-50,-40,-30,-20,-20,-30,-40,-50,-30,-20,-10,0,0,-10,-20,-30,-30,-10,20,30,30,20,-10,-30,-30,-10,30,40,40,30,-10,-30,-30,-10,30,40,40,30,-10,-30,-30,-10,20,30,30,20,-10,-30,-30,-30,0,0,0,0,-30,-30,-50,-30,-30,-30,-30,-30,-30,-50};
const int mirror_table[64] = {56,57,58,59,60,61,62,63,48,49,50,51,52,53,54,55,40,41,42,43,44,45,46,47,32,33,34,35,36,37,38,39,24,25,26,27,28,29,30,31,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7};


struct BoardState {
    U64 bitboards[12];
    U64 occupancies[3];
    int side_to_move;
    int enpassant_sq;
    int castle_rights;
};



class BitboardBoard {
public:
    U64 bitboards[12];
    U64 occupancies[3];
    
    int side_to_move = WHITE;
    int enpassant_sq = NO_SQ;
    int castle_rights = 15; 

    BitboardBoard();
    void print(std::ofstream& file) const;
    void generateMoves(std::vector<Move>& moves);
    void makeMove(const Move& move);
    int evaluate();
    bool isSquareAttacked(int square, int attacker_color) const;
    int getPieceOnSquare(int sq) const;
    
    BoardState getState() const;
    void setState(const BoardState& state);
    std::vector<Move> getValidMoves();
};


class PGNParser {
public:
    static std::vector<std::string> parse(const std::string& pgn_text) {
        std::vector<std::string> moves;
        std::string clean_pgn = pgn_text;

        
        std::replace(clean_pgn.begin(), clean_pgn.end(), '\t', ' ');
        std::replace(clean_pgn.begin(), clean_pgn.end(), '\n', ' ');
        std::replace(clean_pgn.begin(), clean_pgn.end(), '\r', ' ');
        
        std::string nbsp = "\xC2\xA0";
        size_t pos;
        while ((pos = clean_pgn.find(nbsp)) != std::string::npos) {
            clean_pgn.replace(pos, nbsp.length(), " ");
        }

        std::stringstream ss(clean_pgn);
        std::string token;
        while (ss >> token) {
            
            if (token.back() == '.') continue;
            
            if (token == "1-0" || token == "0-1" || token == "1/2-1/2") continue;
            token.erase(std::remove_if(token.begin(), token.end(), [](char c){ return c == '+' || c == '#'; }), token.end());
            moves.push_back(token);
        }
        return moves;
    }
};

BitboardBoard::BitboardBoard() {
    for (int i=0; i<12; ++i) bitboards[i] = 0ULL;
    for (int i=0; i<3; ++i) occupancies[i] = 0ULL;
    const char setup[64] = {
        'R', 'N', 'B', 'Q', 'K', 'B', 'N', 'R',
        'P', 'P', 'P', 'P', 'P', 'P', 'P', 'P',
        ' ',' ',' ',' ',' ',' ',' ',' ',
        ' ',' ',' ',' ',' ',' ',' ',' ',
        ' ',' ',' ',' ',' ',' ',' ',' ',
        ' ',' ',' ',' ',' ',' ',' ',' ',
        'p', 'p', 'p', 'p', 'p', 'p', 'p', 'p',
        'r', 'n', 'b', 'q', 'k', 'b', 'n', 'r'
    };
    std::map<char, Piece> char_to_piece = {{'P', P},{'N', N},{'B', B},{'R', R},{'Q', Q},{'K', K},{'p', p},{'n', n},{'b', b},{'r', r},{'q', q},{'k', k}};
    for (int i = 0; i < 64; ++i) {
        if (setup[i] != ' ') {
            Piece pc = char_to_piece[setup[i]];
            set_bit(bitboards[pc], i);
        }
    }
    for(int i = P; i <= K; ++i) occupancies[WHITE] |= bitboards[i];
    for(int i = p; i <= k; ++i) occupancies[BLACK] |= bitboards[i];
    occupancies[BOTH] = occupancies[WHITE] | occupancies[BLACK];
}

void BitboardBoard::print(std::ofstream& file) const {
    file << "\n  +-----------------+" << std::endl;
    for (int r = 7; r >= 0; --r) {
        file << r + 1 << " | ";
        for (int c = 0; c < 8; ++c) {
            int sq = r * 8 + c;
            char piece_char = '.';
            int piece = getPieceOnSquare(sq);
            if(piece != NO_PIECE) piece_char = "PNBRQKpnbrqk"[piece];
            file << piece_char << " ";
        }
        file << "|" << std::endl;
    }
    file << "  +-----------------+" << std::endl;
    file << "    a b c d e f g h" << std::endl;
    file << "Turn: " << (side_to_move == WHITE ? "White" : "Black") << std::endl;
}

bool BitboardBoard::isSquareAttacked(int square, int attacker_color) const {
    if ((pawn_attacks[1-attacker_color][square] & bitboards[attacker_color == WHITE ? P : p])) return true;
    if ((knight_attacks[square] & bitboards[attacker_color == WHITE ? N : n])) return true;
    if ((king_attacks[square] & bitboards[attacker_color == WHITE ? K : k])) return true;
    if ((get_bishop_attacks(square, occupancies[BOTH]) & (bitboards[attacker_color == WHITE ? B : b] | bitboards[attacker_color == WHITE ? Q : q]))) return true;
    if ((get_rook_attacks(square, occupancies[BOTH]) & (bitboards[attacker_color == WHITE ? R : r] | bitboards[attacker_color == WHITE ? Q : q]))) return true;
    return false;
}

int BitboardBoard::getPieceOnSquare(int sq) const {
    for(int piece=P; piece<=k; ++piece){
        if(get_bit(bitboards[piece], sq)) return piece;
    }
    return NO_PIECE;
}

std::vector<Move> BitboardBoard::getValidMoves() {
    std::vector<Move> legal_moves;
    generateMoves(legal_moves);
    std::vector<Move> valid_moves;
    BoardState original_state = getState();

    for (const auto& move : legal_moves) {
        makeMove(move);
        int king_sq = lsb_index(bitboards[original_state.side_to_move == WHITE ? K : k]);
        if(!isSquareAttacked(king_sq, 1-original_state.side_to_move)) {
            valid_moves.push_back(move);
        }
        setState(original_state);
    }
    return valid_moves;
}


void BitboardBoard::generateMoves(std::vector<Move>& moves) {
    U64 current_pieces, attacks;
    int source_sq, target_sq;

    for (int piece = (side_to_move == WHITE ? P : p); piece <= (side_to_move == WHITE ? K : k); ++piece) {
        current_pieces = bitboards[piece];
        while (current_pieces) {
            source_sq = lsb_index(current_pieces);
            if (piece == P) { 
                if (!(get_bit(occupancies[BOTH], source_sq + 8))) {
                    if (source_sq >= A7 && source_sq <= H7) { 
                        moves.push_back({source_sq, source_sq + 8, P, Q});
                    } else moves.push_back({source_sq, source_sq + 8, P});
                    if (source_sq >= A2 && source_sq <= H2 && !get_bit(occupancies[BOTH], source_sq + 16)) {
                         moves.push_back({source_sq, source_sq + 16, P, NO_PIECE, NO_PIECE, 1});
                    }
                }
                attacks = pawn_attacks[WHITE][source_sq] & occupancies[BLACK];
                while(attacks) {
                    target_sq = lsb_index(attacks);
                    int captured = getPieceOnSquare(target_sq);
                    if (source_sq >= A7 && source_sq <= H7) { 
                         moves.push_back({source_sq, target_sq, P, Q, captured});
                    } else moves.push_back({source_sq, target_sq, P, NO_PIECE, captured});
                    pop_bit(attacks, target_sq);
                }
                if(enpassant_sq != NO_SQ && (pawn_attacks[WHITE][source_sq] & (1ULL << enpassant_sq))) {
                    moves.push_back({source_sq, enpassant_sq, P, NO_PIECE, p, 0, 1});
                }
            } else if (piece == p) { 
                 if (!(get_bit(occupancies[BOTH], source_sq - 8))) {
                    if (source_sq >= A2 && source_sq <= H2) {
                        moves.push_back({source_sq, source_sq - 8, p, q});
                    } else moves.push_back({source_sq, source_sq - 8, p});
                    if (source_sq >= A7 && source_sq <= H7 && !get_bit(occupancies[BOTH], source_sq - 16)) {
                        moves.push_back({source_sq, source_sq - 16, p, NO_PIECE, NO_PIECE, 1});
                    }
                }
                attacks = pawn_attacks[BLACK][source_sq] & occupancies[WHITE];
                while(attacks) {
                    target_sq = lsb_index(attacks);
                    int captured = getPieceOnSquare(target_sq);
                    if (source_sq >= A2 && source_sq <= H2) {
                         moves.push_back({source_sq, target_sq, p, q, captured});
                    } else moves.push_back({source_sq, target_sq, p, NO_PIECE, captured});
                    pop_bit(attacks, target_sq);
                }
                 if(enpassant_sq != NO_SQ && (pawn_attacks[BLACK][source_sq] & (1ULL << enpassant_sq))) {
                    moves.push_back({source_sq, enpassant_sq, p, NO_PIECE, P, 0, 1});
                }
            } else { 
                attacks = (piece == N || piece == n) ? knight_attacks[source_sq] :
                          (piece == K || piece == k) ? king_attacks[source_sq] :
                          (piece == B || piece == b) ? get_bishop_attacks(source_sq, occupancies[BOTH]) :
                          (piece == R || piece == r) ? get_rook_attacks(source_sq, occupancies[BOTH]) :
                          get_bishop_attacks(source_sq, occupancies[BOTH]) | get_rook_attacks(source_sq, occupancies[BOTH]);
                
                attacks &= ~(side_to_move == WHITE ? occupancies[WHITE] : occupancies[BLACK]);
                
                while(attacks) {
                    target_sq = lsb_index(attacks);
                    int captured = getPieceOnSquare(target_sq);
                    moves.push_back({source_sq, target_sq, piece, NO_PIECE, captured});
                    pop_bit(attacks, target_sq);
                }
            }
            pop_bit(current_pieces, source_sq);
        }
    }
    
    if(side_to_move == WHITE) {
        if(castle_rights & WK) {
            if(!get_bit(occupancies[BOTH], F1) && !get_bit(occupancies[BOTH], G1) &&
               !isSquareAttacked(E1, BLACK) && !isSquareAttacked(F1, BLACK)) {
                moves.push_back({E1, G1, K, NO_PIECE, NO_PIECE, 0, 0, 1});
            }
        }
        if(castle_rights & WQ) {
             if(!get_bit(occupancies[BOTH], D1) && !get_bit(occupancies[BOTH], C1) && !get_bit(occupancies[BOTH], B1) &&
               !isSquareAttacked(E1, BLACK) && !isSquareAttacked(D1, BLACK)) {
                moves.push_back({E1, C1, K, NO_PIECE, NO_PIECE, 0, 0, 1});
            }
        }
    } else {
        if(castle_rights & BK) {
             if(!get_bit(occupancies[BOTH], F8) && !get_bit(occupancies[BOTH], G8) &&
               !isSquareAttacked(E8, WHITE) && !isSquareAttacked(F8, WHITE)) {
                moves.push_back({E8, G8, k, NO_PIECE, NO_PIECE, 0, 0, 1});
            }
        }
        if(castle_rights & BQ) {
             if(!get_bit(occupancies[BOTH], D8) && !get_bit(occupancies[BOTH], C8) && !get_bit(occupancies[BOTH], B8) &&
               !isSquareAttacked(E8, WHITE) && !isSquareAttacked(D8, WHITE)) {
                moves.push_back({E8, C8, k, NO_PIECE, NO_PIECE, 0, 0, 1});
            }
        }
    }
}


int BitboardBoard::evaluate() {
    int score = 0;
    U64 piece_bb;
    int piece_sq;

    for (int piece = P; piece <= k; ++piece) {
        piece_bb = bitboards[piece];
        while(piece_bb) {
            piece_sq = lsb_index(piece_bb);
            int piece_value = piece_values[piece % 6];
            int sign = (piece < p) ? 1 : -1;
            score += piece_value * sign;
            if(piece == P) score += pawn_table[piece_sq];
            else if(piece == p) score -= pawn_table[mirror_table[piece_sq]];
            else if(piece == N) score += knight_table[piece_sq];
            else if(piece == n) score -= knight_table[mirror_table[piece_sq]];
            else if(piece == B) score += bishop_table[piece_sq];
            else if(piece == b) score -= bishop_table[mirror_table[piece_sq]];
            else if(piece == R) score += rook_table[piece_sq];
            else if(piece == r) score -= rook_table[mirror_table[piece_sq]];
            else if(piece == K) score += king_table[piece_sq];
            else if(piece == k) score -= king_table[mirror_table[piece_sq]];
            pop_bit(piece_bb, piece_sq);
        }
    }
    return (side_to_move == WHITE) ? score : -score;
}

BoardState BitboardBoard::getState() const {
    BoardState state;
    for(int i=0; i<12; ++i) state.bitboards[i] = bitboards[i];
    for(int i=0; i<3; ++i) state.occupancies[i] = occupancies[i];
    state.side_to_move = side_to_move;
    state.enpassant_sq = enpassant_sq;
    state.castle_rights = castle_rights;
    return state;
}

void BitboardBoard::setState(const BoardState& state) {
    for(int i=0; i<12; ++i) bitboards[i] = state.bitboards[i];
    for(int i=0; i<3; ++i) occupancies[i] = state.occupancies[i];
    side_to_move = state.side_to_move;
    enpassant_sq = state.enpassant_sq;
    castle_rights = state.castle_rights;
}


void BitboardBoard::makeMove(const Move& move) {
    pop_bit(bitboards[move.piece], move.from_sq);

    if(move.captured_piece != NO_PIECE) {
        pop_bit(bitboards[move.captured_piece], move.to_sq);
    }
    set_bit(bitboards[move.piece], move.to_sq);
    
    if(move.promotion != NO_PIECE) {
        pop_bit(bitboards[move.piece], move.to_sq);
        set_bit(bitboards[side_to_move == WHITE ? move.promotion : (Piece)(move.promotion+6)], move.to_sq);
    }

    if(move.enpassant) {
        if(side_to_move == WHITE) pop_bit(bitboards[p], move.to_sq - 8);
        else pop_bit(bitboards[P], move.to_sq + 8);
    }
    enpassant_sq = NO_SQ;
    if(move.double_push) {
        enpassant_sq = (side_to_move == WHITE) ? move.to_sq - 8 : move.to_sq + 8;
    }
    
    if(move.castling) {
        switch(move.to_sq) {
            case G1: pop_bit(bitboards[R], H1); set_bit(bitboards[R], F1); break;
            case C1: pop_bit(bitboards[R], A1); set_bit(bitboards[R], D1); break;
            case G8: pop_bit(bitboards[r], H8); set_bit(bitboards[r], F8); break;
            case C8: pop_bit(bitboards[r], A8); set_bit(bitboards[r], D8); break;
        }
    }
    
    castle_rights &= ~( (move.from_sq == E1) * (WK | WQ) | (move.from_sq == E8) * (BK | BQ) );
    castle_rights &= ~( (move.from_sq == H1 || move.to_sq == H1) * WK );
    castle_rights &= ~( (move.from_sq == A1 || move.to_sq == A1) * WQ );
    castle_rights &= ~( (move.from_sq == H8 || move.to_sq == H8) * BK );
    castle_rights &= ~( (move.from_sq == A8 || move.to_sq == A8) * BQ );

    occupancies[WHITE] = 0ULL; occupancies[BLACK] = 0ULL;
    for(int i = P; i <= K; ++i) occupancies[WHITE] |= bitboards[i];
    for(int i = p; i <= k; ++i) occupancies[BLACK] |= bitboards[i];
    occupancies[BOTH] = occupancies[WHITE] | occupancies[BLACK];
    
    side_to_move = 1 - side_to_move;
}



class Engine {
public:
    long long nodes_searched = 0;
    std::pair<Move, int> findBestMove(BitboardBoard& board, int depth);
    int evaluatePosition(BitboardBoard& board, int depth);
    long long getNodesSearched() const { return nodes_searched; }
private:
    int minimax(BitboardBoard& board, int depth, int alpha, int beta);
    int quiescenceSearch(BitboardBoard& board, int alpha, int beta);
};

std::pair<Move, int> Engine::findBestMove(BitboardBoard& board, int depth) {
    Move best_move;
    int best_value = -INF -1;
    std::vector<Move> moves = board.getValidMoves();
    
    BoardState original_state = board.getState();

    for (const auto& move : moves) {
        board.makeMove(move);
        int board_value = -minimax(board, depth - 1, -INF, INF);
        board.setState(original_state);
        
        if (board_value > best_value) {
            best_value = board_value;
            best_move = move;
        }
    }
    return { best_move, best_value };
}

int Engine::evaluatePosition(BitboardBoard& board, int depth) {
    return minimax(board, depth, -INF, INF);
}

int Engine::minimax(BitboardBoard& board, int depth, int alpha, int beta) {
    nodes_searched++;
    if(depth == 0) return quiescenceSearch(board, alpha, beta);

    std::vector<Move> moves;
    board.generateMoves(moves);
    BoardState original_state = board.getState();
    int legal_moves_played = 0;

    for(const auto& move : moves) {
        board.makeMove(move);
        int king_sq = lsb_index(board.bitboards[original_state.side_to_move == WHITE ? K : k]);
        if(board.isSquareAttacked(king_sq, 1 - original_state.side_to_move)) {
            board.setState(original_state);
            continue;
        }
        legal_moves_played++;
        
        int score = -minimax(board, depth - 1, -beta, -alpha);
        board.setState(original_state);

        if(score >= beta) return beta;
        if(score > alpha) alpha = score;
    }

    if(legal_moves_played == 0) {
        int king_sq = lsb_index(board.bitboards[board.side_to_move == WHITE ? K : k]);
        if(board.isSquareAttacked(king_sq, 1 - board.side_to_move)) return -INF; 
        return 0; 
    }

    return alpha;
}

int Engine::quiescenceSearch(BitboardBoard& board, int alpha, int beta) {
    nodes_searched++;
    int stand_pat = board.evaluate();
    if(stand_pat >= beta) return beta;
    if(alpha < stand_pat) alpha = stand_pat;

    std::vector<Move> moves;
    board.generateMoves(moves);
    BoardState original_state = board.getState();

    for(const auto& move : moves) {
        if(move.captured_piece == NO_PIECE) continue;

        board.makeMove(move);
        int king_sq = lsb_index(board.bitboards[original_state.side_to_move == WHITE ? K : k]);
        if(board.isSquareAttacked(king_sq, 1 - original_state.side_to_move)) {
            board.setState(original_state);
            continue;
        }
        
        int score = -quiescenceSearch(board, -beta, -alpha);
        board.setState(original_state);

        if(score >= beta) return beta;
        if(score > alpha) alpha = score;
    }
    return alpha;
}


Move sanToMove(BitboardBoard& board, const std::string& san) {
    std::vector<Move> valid_moves = board.getValidMoves();
    
    if (san == "O-O") {
        for(const auto& move : valid_moves) if(move.castling && move.to_sq > move.from_sq) return move;
    }
    if (san == "O-O-O") {
        for(const auto& move : valid_moves) if(move.castling && move.to_sq < move.from_sq) return move;
    }

    char target_piece_char = 'P';
    Piece promotion_p = NO_PIECE;
    char from_file_hint = 0, from_rank_hint = 0;
    int to_c = -1, to_r = -1;
    
    std::string temp_san = san;
    if (temp_san.find('=') != std::string::npos) {
        char promo_char = temp_san.back();
        if(promo_char == 'Q' || promo_char == 'q') promotion_p = Q; else if (promo_char == 'R' || promo_char == 'r') promotion_p = R;
        temp_san.pop_back(); temp_san.pop_back();
    }
    
    if (temp_san.length() >= 2) {
        char dest_file = temp_san[temp_san.length() - 2];
        char dest_rank = temp_san[temp_san.length() - 1];
        if (dest_file >= 'a' && dest_file <= 'h' && dest_rank >= '1' && dest_rank <= '8') {
            to_c = dest_file - 'a';
            to_r = dest_rank - '1';
            temp_san.pop_back();
            temp_san.pop_back();
        }
    }
    
    if (!temp_san.empty() && isupper(temp_san[0])) {
        target_piece_char = temp_san[0];
        temp_san.erase(0, 1);
    }
    
    bool is_capture_san = false;
    size_t capture_pos = temp_san.find('x');
    if (capture_pos != std::string::npos) {
        is_capture_san = true;
        temp_san.erase(capture_pos, 1);
    }
    if (target_piece_char == 'P' && temp_san.length() > 0 && temp_san[0] >= 'a' && temp_san[0] <= 'h' && !isdigit(temp_san[0])) {
        is_capture_san = true;
    }


    for (char c : temp_san) {
        if (c >= 'a' && c <= 'h') from_file_hint = c;
        if (c >= '1' && c <= '8') from_rank_hint = c;
    }

    std::map<char, Piece> char_to_piece_map = {{'P',P},{'N',N},{'B',B},{'R',R},{'Q',Q},{'K',K}};
    Piece target_piece = char_to_piece_map[target_piece_char];
    if (board.side_to_move == BLACK) target_piece = (Piece)(target_piece + 6);

    std::vector<Move> candidates;
    for (const auto& move : valid_moves) {
        if (move.to_sq == (to_r * 8 + to_c) && move.piece == target_piece) {
             bool move_is_capture = (move.captured_piece != NO_PIECE || move.enpassant);
             if (is_capture_san != move_is_capture) continue;

             if (promotion_p == NO_PIECE || (Piece)(move.promotion) == (Piece)(promotion_p)) {
                 candidates.push_back(move);
             }
        }
    }
    
    if (candidates.empty()) throw std::runtime_error("No legal move found for " + san);
    if (candidates.size() == 1) return candidates[0];

    if (from_file_hint) {
        candidates.erase(std::remove_if(candidates.begin(), candidates.end(),
            [=](const Move& m) { return ((m.from_sq % 8) + 'a') != from_file_hint; }), candidates.end());
    }
    if (from_rank_hint) {
        candidates.erase(std::remove_if(candidates.begin(), candidates.end(),
            [=](const Move& m) { return ((m.from_sq / 8) + '1') != from_rank_hint; }), candidates.end());
    }
    
    if (candidates.size() == 1) return candidates[0];

    throw std::runtime_error("Could not parse ambiguous SAN move: " + san);
}


void printProgressBar(float progress) {
    int barWidth = 50;
    std::cout << "[";
    int pos = barWidth * progress;
    for (int i = 0; i < barWidth; ++i) {
        if (i < pos) std::cout << "=";
        else if (i == pos) std::cout << ">";
        else std::cout << " ";
    }
    std::cout << "] " << int(progress * 100.0) << " %\r";
    std::cout.flush();
}



int main() {
    initialize_leaper_attacks();
    
    std::ifstream input_file("input.txt");
    if (!input_file.is_open()) {
        std::cerr << "Error: Could not open input.txt." << std::endl;
        return 1;
    }

    int search_depth;
    std::string pgn_text;

    if (!(input_file >> search_depth)) {
        std::cerr << "Error: Could not read search depth from input.txt." << std::endl;
        return 1;
    }
    input_file.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
    std::getline(input_file, pgn_text);
    input_file.close();

    std::ofstream output_file("output.txt");
     if (!output_file.is_open()) {
        std::cerr << "Error: Could not open output.txt for writing." << std::endl;
        return 1;
    }

    std::vector<std::string> san_moves = PGNParser::parse(pgn_text);

    BitboardBoard board;
    Engine engine;
    
    output_file << "--- Chess PGN Analyzer ---" << std::endl;
    output_file << "Analyzing game at depth " << search_depth << "..." << std::endl;
    
    auto start_time = std::chrono::high_resolution_clock::now();
    
    std::cout << "Analyzing... " << std::endl;

    for (size_t i = 0; i < san_moves.size(); ++i) {
        std::string san = san_moves[i];
        
        output_file << "\n========================================\n";
        output_file << "Move " << (i/2) + 1 << " (" << (board.side_to_move == WHITE ? "White" : "Black") << ")\n";
        
        try {
            std::vector<Move> valid_moves = board.getValidMoves();
            Move human_move = sanToMove(board, san);

            output_file << "Move Played: " << san << " (" << human_move.toString() << ")\n";
            output_file << "----------------------------------------\n";
            output_file << "All Legal Moves (" << valid_moves.size() << "):\n";
            for(size_t j = 0; j < valid_moves.size(); ++j) {
                output_file << valid_moves[j].toString() << (((j+1) % 10 == 0) ? "\n" : " ");
            }
            output_file << "\n----------------------------------------\n";
            
            auto engine_choice = engine.findBestMove(board, search_depth);
            Move best_move = engine_choice.first;
            int eval_before = engine_choice.second;
            
            BoardState state_before_move = board.getState();
            board.makeMove(human_move);
            
            int eval_after = -engine.evaluatePosition(board, search_depth);
            board.setState(state_before_move);
            
            double eval_drop = (double)(eval_before - eval_after);
            
            output_file << "Analysis:\n";
            if (eval_drop >= BLUNDER_THRESHOLD) {
                output_file << "  - Status: ?? Blunder\n";
            } else if (eval_drop >= INACCURACY_THRESHOLD) {
                output_file << "  - Status: ?! Inaccuracy\n";
            } else {
                output_file << "  - Status: !! Best Move\n";
            }
            output_file << "  - Eval Drop: " << (eval_drop / 100.0) << "\n";
            output_file << "  - Engine's Choice: " << best_move.toString() << "\n";
            
            board.makeMove(human_move);
        
        } catch (const std::runtime_error& e) {
            output_file << "\nERROR: " << e.what() << ". Stopping analysis." << std::endl;
            break;
        }

        printProgressBar((float)(i + 1) / san_moves.size());
    }
    
    auto end_time = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> duration = end_time - start_time;
    
    std::cout << std::endl;  
    
    output_file << "\n========================================\n";
    output_file << "\nAnalysis complete." << std::endl;

    output_file << "\n--- Analysis Summary ---\n";
    output_file << "Total Positions Analyzed: " << engine.getNodesSearched() << "\n";
    output_file << "Total Time Taken: " << duration.count() << " seconds\n";
    
    output_file << "\nFinal Board Position:";
    board.print(output_file);

    output_file.close();
    std::cout << "Analysis complete. Output written to output.txt" << std::endl;

    return 0;
}

