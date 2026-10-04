#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum {
    CUBIES = 7,
    PERMUTATIONS = 5040,
    ORIENTATIONS = 729,
    STATES = PERMUTATIONS * ORIENTATIONS,
    MOVES = 9
};

typedef struct {
    uint8_t p[CUBIES], o[CUBIES];
} state_t;

/*@ predicate valid_state(state_t *state) =
      (\forall integer i; 0 <= i < CUBIES ==>
         state->p[i] < CUBIES && state->o[i] < 3) &&
      (\forall integer i, j; 0 <= i < j < CUBIES ==>
         state->p[i] != state->p[j]) &&
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
 */

static const char *const move_names[MOVES] = {"R",  "R2", "R'", "B", "B2",
                                              "B'", "D",  "D2", "D'"};
static const uint8_t inverse_move[MOVES] = {2, 1, 0, 5, 4, 3, 8, 7, 6};
/* Each destination takes a cubie from source[face][destination]. */
static const uint8_t source[3][CUBIES] = {
    {1, 4, 2, 0, 3, 5, 6},
    {0, 1, 2, 4, 5, 6, 3},
    {0, 2, 5, 3, 1, 4, 6},
};
static const uint8_t twist[3][CUBIES] = {
    {1, 2, 0, 2, 1, 0, 0},
    {0, 0, 0, 1, 2, 1, 2},
    {0, 0, 0, 0, 0, 0, 0},
};

/* The three quarter-turns preserve the fixed front-upper-left corner. */
/*@ requires face < 3;
    assigns \nothing;
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.p[i] == state.p[source[face][i]];
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.o[i] == (state.o[source[face][i]] + twist[face][i]) % 3;
 */
static state_t quarter_turn(state_t state, uint8_t face)
{
    state_t result;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant \forall integer j; 0 <= j < i ==>
          result.p[j] == state.p[source[face][j]];
        loop invariant \forall integer j; 0 <= j < i ==>
          result.o[j] == (state.o[source[face][j]] + twist[face][j]) % 3;
        loop assigns i, result.p[0..6], result.o[0..6];
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t from = source[face][i];
        result.p[i] = state.p[from];
        result.o[i] = (uint8_t) ((state.o[from] + twist[face][i]) % 3U);
    }
    return result;
}

static state_t apply_move(state_t state, uint8_t move)
{
    uint8_t turns = (uint8_t) (move % 3U + 1U);
    for (uint8_t i = 0; i < turns; ++i)
        state = quarter_turn(state, (uint8_t) (move / 3U));
    return state;
}

/*@ requires \valid_read(state);
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->p[i] < CUBIES;
    requires \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->o[i] < 3;
    assigns \nothing;
    ensures \result < STATES;
 */
static uint32_t rank_state(const state_t *state)
{
    uint32_t p = 0, o = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant (i == 0 ==> p == 0) && (i == 1 ==> p <= 6) &&
          (i == 2 ==> p <= 41) && (i == 3 ==> p <= 209) &&
          (i == 4 ==> p <= 839) && (i == 5 ==> p <= 2519) &&
          (i >= 6 ==> p <= 5039);
        loop assigns i, p;
        loop variant CUBIES - i;
     */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t smaller = 0;
        /*@ loop invariant i + 1 <= j <= CUBIES;
            loop invariant smaller <= j - i - 1;
            loop assigns j, smaller;
            loop variant CUBIES - j;
         */
        for (uint8_t j = (uint8_t) (i + 1U); j < CUBIES; ++j)
            if (state->p[j] < state->p[i])
                ++smaller;
        p = p * (CUBIES - i) + smaller;
    }
    /*@ loop invariant 0 <= i <= 6;
        loop invariant (i == 0 ==> o == 0) && (i == 1 ==> o < 3) &&
          (i == 2 ==> o < 9) && (i == 3 ==> o < 27) &&
          (i == 4 ==> o < 81) && (i == 5 ==> o < 243) &&
          (i == 6 ==> o < 729);
        loop assigns i, o;
        loop variant 6 - i;
     */
    for (uint8_t i = 0; i < 6; ++i)
        o = o * 3U + state->o[i];
    return p * ORIENTATIONS + o;
}

#define PATTERN_STATES 68040

static uint32_t pattern_rank(const state_t *state)
{
    uint8_t selected[4];
    uint8_t selected_count = 0;

    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (state->p[i] < 4)
            selected[selected_count++] = i;
    }

    uint32_t combination_rank = 0;

    for (int a = 0; a < 7; ++a) {
        for (int b = a + 1; b < 7; ++b) {
            for (int c = b + 1; c < 7; ++c) {
                for (int d = c + 1; d < 7; ++d) {
                    if (a == selected[0] &&
                        b == selected[1] &&
                        c == selected[2] &&
                        d == selected[3])
                        goto combination_found;

                    ++combination_rank;
                }
            }
        }
    }

combination_found: ;

    uint8_t order[4];
    uint8_t count = 0;

    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (state->p[i] < 4)
            order[count++] = state->p[i];
    }

    uint32_t perm_rank = 0;

    for (uint8_t i = 0; i < 4; ++i) {
        uint8_t smaller = 0;

        for (uint8_t j = (uint8_t)(i + 1U); j < 4; ++j) {
            if (order[j] < order[i])
                ++smaller;
        }

        perm_rank = perm_rank * (4 - i) + smaller;
    }

    uint32_t orientation_rank = 0;

    for (uint8_t i = 0; i < 4; ++i) {
        orientation_rank =
            orientation_rank * 3U + state->o[selected[i]];
    }

    uint32_t placement_rank = combination_rank * 24U + perm_rank;

    return placement_rank * 81U + orientation_rank;
}

static void pattern_unrank(uint32_t rank, state_t *state)
{
    uint32_t orientation_rank = rank % 81U;
    uint32_t placement_rank = rank / 81U;

    uint32_t perm_rank = placement_rank % 24U;
    uint32_t combination_rank = placement_rank / 24U;

    for (uint8_t i = 0; i < CUBIES; ++i) {
        state->p[i] = 4;
        state->o[i] = 0;
    }

    uint8_t selected[4] = {0};
    uint32_t current_rank = 0;
    uint8_t found = 0;

    for (uint8_t a = 0; a < 7 && !found; ++a) {
        for (uint8_t b = (uint8_t)(a + 1U); b < 7 && !found; ++b) {
            for (uint8_t c = (uint8_t)(b + 1U); c < 7 && !found; ++c) {
                for (uint8_t d = (uint8_t)(c + 1U); d < 7; ++d) {

                    if (current_rank == combination_rank) {
                        selected[0] = a;
                        selected[1] = b;
                        selected[2] = c;
                        selected[3] = d;
                        found = 1;
                        break;
                    }

                    ++current_rank;
                }
            }
        }
    }

    uint8_t order[4];

    uint8_t d0 = (uint8_t)(perm_rank / 6U);
    perm_rank %= 6U;

    uint8_t d1 = (uint8_t)(perm_rank / 2U);
    perm_rank %= 2U;

    uint8_t d2 = (uint8_t)perm_rank;

    uint8_t digits[4] = {d0, d1, d2, 0};
    uint8_t available[4] = {0, 1, 2, 3};

    for (uint8_t i = 0; i < 4; ++i) {
        uint8_t index = digits[i];

        order[i] = available[index];

        for (uint8_t j = index; j < 3U; ++j)
            available[j] = available[j + 1U];
    }


    for (uint8_t i = 0; i < 4; ++i)
        state->p[selected[i]] = order[i];

    for (int i = 3; i >= 0; --i) {
        state->o[selected[i]] =
            (uint8_t)(orientation_rank % 3U);

        orientation_rank /= 3U;
    }
}

static uint8_t pdb[PATTERN_STATES];

static void build_pdb(void)
{
    memset(pdb, 0xFF, sizeof pdb);

    uint32_t queue[PATTERN_STATES];
    uint32_t head = 0;
    uint32_t tail = 0;

    state_t solved = {
        {0, 1, 2, 3, 4, 5, 6},
        {0}
    };

    uint32_t start = pattern_rank(&solved);
    pdb[start] = 0;
    queue[tail++] = start;

    while (head < tail) {
        uint32_t rank = queue[head++];
        uint8_t distance = pdb[rank];

        state_t state;
        pattern_unrank(rank, &state);

        for (uint8_t move = 0; move < MOVES; ++move) {
            state_t next = apply_move(state, move);
            uint32_t next_rank = pattern_rank(&next);

            if (pdb[next_rank] == 0xFF) {
                pdb[next_rank] = (uint8_t)(distance + 1U);
                queue[tail++] = next_rank;
            }
        }
    }

    for (uint32_t i = 0; i < PATTERN_STATES; ++i) {
        if (pdb[i] == 0xFF) {
            fprintf(stderr, "PDB incomplete at %u\n", i);
            exit(EXIT_FAILURE);
        }
    }
}

/*@ requires \valid(state); requires rank < STATES; assigns *state; */
static void unrank_state(uint32_t rank, state_t *state)
{
    uint8_t available[CUBIES] = {0, 1, 2, 3, 4, 5, 6};
    uint32_t p = rank / ORIENTATIONS, o = rank % ORIENTATIONS, f = 720;
    uint8_t sum = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t q = (uint8_t) (p / f);
        p %= f;
        state->p[i] = available[q];
        for (uint8_t j = q; j + 1U < CUBIES - i; ++j)
            available[j] = available[j + 1U];
        if (i < 5)
            f /= 6U - i;
    }
    for (uint8_t i = 6; i-- > 0;) {
        state->o[i] = (uint8_t) (o % 3U);
        sum = (uint8_t) (sum + state->o[i]);
        o /= 3U;
    }
    state->o[6] = (uint8_t) ((3U - sum % 3U) % 3U);
}

/*@ requires \valid_read(state);
    requires \initialized(&state->p[0..6]) && \initialized(&state->o[0..6]);
    assigns \nothing;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures complete: valid_state(state) ==> \result != 0;
 */
static int valid(const state_t *state)
{
    uint8_t sum = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant sum <= 2 * i;
        loop invariant sum == (i > 0 ? state->o[0] : 0) +
          (i > 1 ? state->o[1] : 0) + (i > 2 ? state->o[2] : 0) +
          (i > 3 ? state->o[3] : 0) + (i > 4 ? state->o[4] : 0) +
          (i > 5 ? state->o[5] : 0) + (i > 6 ? state->o[6] : 0);
        loop invariant \forall integer j; 0 <= j < i ==>
          state->p[j] < CUBIES && state->o[j] < 3;
        loop invariant \forall integer j, k; 0 <= j < k < i ==>
          state->p[j] != state->p[k];
        loop assigns i, sum;
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (state->p[i] >= CUBIES || state->o[i] >= 3)
            return 0;
        /*@ loop invariant 0 <= j <= i;
            loop invariant \forall integer k; 0 <= k < j ==>
              state->p[k] != state->p[i];
            loop assigns j;
            loop variant i - j;
        */
        for (uint8_t j = 0; j < i; ++j)
            if (state->p[j] == state->p[i])
                return 0;
        sum = (uint8_t) (sum + state->o[i]);
    }
    return sum % 3U == 0;
}

static uint8_t *build_table(uint8_t *diameter)
{
    uint8_t *toward_solved = malloc(STATES);
    uint32_t *queue = malloc((size_t) STATES * sizeof *queue);
    uint16_t permutation[3][PERMUTATIONS], orientation[3][ORIENTATIONS];
    uint32_t head = 0, tail = 1, level_end = 1;
    state_t state;
    if (!toward_solved || !queue) {
        free(toward_solved);
        free(queue);
        return NULL;
    }
    for (uint16_t rank = 0; rank < PERMUTATIONS; ++rank) {
        unrank_state((uint32_t) rank * ORIENTATIONS, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            permutation[face][rank] =
                (uint16_t) (rank_state(&next) / ORIENTATIONS);
        }
    }
    for (uint16_t rank = 0; rank < ORIENTATIONS; ++rank) {
        unrank_state(rank, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            orientation[face][rank] =
                (uint16_t) (rank_state(&next) % ORIENTATIONS);
        }
    }
    memset(toward_solved, UINT8_MAX, STATES);
    queue[0] = 0;
    toward_solved[0] = 0;
    *diameter = 0;
    while (head < tail) {
        if (head == level_end) {
            level_end = tail;
            ++*diameter;
        }
        uint32_t here = queue[head++];
        uint16_t p = (uint16_t) (here / ORIENTATIONS);
        uint16_t o = (uint16_t) (here % ORIENTATIONS);
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next_p = p, next_o = o;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next_p = permutation[face][next_p];
                next_o = orientation[face][next_o];
                uint32_t there = (uint32_t) next_p * ORIENTATIONS + next_o;
                if (toward_solved[there] == UINT8_MAX) {
                    uint8_t move = (uint8_t) (face * 3U + turn);
                    toward_solved[there] = inverse_move[move];
                    queue[tail++] = there;
                }
            }
        }
    }
    free(queue);
    if (tail != STATES) {
        free(toward_solved);
        return NULL;
    }
    return toward_solved;
}

/*@ requires valid_read_string(input);
    requires \valid(state);
    assigns state->p[0..6], state->o[0..6];
    ensures \result != 0 ==> input[14] == '\0';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] == input[i] - '1';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->o[i] == input[i + CUBIES] - '1';
 */
static int parse_state(const char *input, state_t *state)
{
    /*@ loop invariant 0 <= i <= 14;
        loop invariant i <= strlen(input);
        loop invariant i <= 7 ==> \initialized(&state->p[0..i-1]);
        loop invariant i >= 7 ==> \initialized(&state->p[0..6]);
        loop invariant i >= 7 ==> \initialized(&state->o[0..i-8]);
        loop invariant \forall integer j; 0 <= j < i && j < CUBIES ==>
          state->p[j] == input[j] - '1';
        loop invariant \forall integer j; 0 <= j < i - CUBIES ==>
          state->o[j] == input[j + CUBIES] - '1';
        loop assigns i, state->p[0..6], state->o[0..6];
        loop variant 14 - i;
     */
    for (int i = 0; i < 14; ++i) {
        int limit = i < 7 ? 7 : 3;
        if (input[i] < '1' || input[i] > '0' + limit)
            return 0;
        (i < 7 ? state->p : state->o)[i % 7] = (uint8_t) (input[i] - '1');
    }
    return input[14] == '\0' && valid(state);
}

/* stdout is fully buffered off a terminal, so a write error surfaces at the
 * flush, not at the printf that queued the bytes. Every exit path that has
 * produced output goes through here.
 */
static int output_failed(void)
{
    return fflush(stdout) != 0 || ferror(stdout);
}

static int self_test(void)
{
    const state_t solved = {{0, 1, 2, 3, 4, 5, 6}, {0}};
    state_t state;

    for (uint8_t move = 0; move < MOVES; ++move) {
        state = solved;
        state = apply_move(state, move);
        state = apply_move(state, inverse_move[move]);
        if (memcmp(&solved, &state, sizeof solved))
            return 0;
    }

    for (uint32_t rank = 0; rank < STATES; ++rank) {
        unrank_state(rank, &state);

        if (!valid(&state) || rank_state(&state) != rank)
            return 0;
    }

    uint32_t pattern = pattern_rank(&solved);

    if (pattern != 0 || pattern >= PATTERN_STATES)
        return 0;

    for (uint32_t rank = 0; rank < PATTERN_STATES; ++rank) {
        pattern_unrank(rank, &state);

        if (pattern_rank(&state) != rank)
            return 0;
    }

    for (uint8_t move = 0; move < MOVES; ++move) {
        state = apply_move(solved, move);
        pattern = pattern_rank(&state);

        if (pattern >= PATTERN_STATES)
            return 0;
    }

    return 1;
}

static void write_pdb_header(void)
{
    FILE *fp = fopen("pdb_data.h", "w");

    if (fp == NULL) {
        perror("fopen");
        exit(EXIT_FAILURE);
    }

    fprintf(fp, "#ifndef PDB_DATA_H\n");
    fprintf(fp, "#define PDB_DATA_H\n\n");

    fprintf(fp, "#include <stdint.h>\n\n");

    fprintf(fp, "static const uint8_t pdb_data[PATTERN_STATES] = {\n");

    for (uint32_t i = 0; i < PATTERN_STATES; ++i) {
        if (i % 16U == 0)
            fprintf(fp, "    ");

        fprintf(fp, "%u", pdb[i]);

        if (i + 1U != PATTERN_STATES)
            fprintf(fp, ", ");

        if (i % 16U == 15U)
            fprintf(fp, "\n");
    }

    if (PATTERN_STATES % 16U != 0)
        fprintf(fp, "\n");

    fprintf(fp, "};\n\n");
    fprintf(fp, "#endif\n");

    fclose(fp);
}

int main(int argc, char *argv[])
{
    if (argc > 1 && !strcmp(argv[1], "--build-pdb")) {
        build_pdb();

        uint8_t max_distance = 0;
        for (uint32_t i = 0; i < PATTERN_STATES; ++i) {
            if (pdb[i] > max_distance)
                max_distance = pdb[i];
        }

        write_pdb_header();

        printf("PDB built: %u states, max distance %u\n",
               PATTERN_STATES, max_distance);

        printf("PDB written to pdb_data.h\n");

        return 0; 
    }

    state_t state;
    uint8_t diameter;
    if (argc == 2 && !strcmp(argv[1], "--self-test")) {
        if (!self_test()) {
            fputs("self-test failed\n", stderr);
            return 1;
        }
        uint8_t *table = build_table(&diameter);
        if (!table) {
            fputs("could not build complete state table\n", stderr);
            return 1;
        }
        free(table);
        if (diameter != 11) {
            fputs("BFS check failed\n", stderr);
            return 1;
        }
        puts("3674160 states; diameter 11");
        return output_failed();
    }
    if (argc != 2 || !parse_state(argv[1], &state)) {
        /* C99 5.1.2.2.1 lets argv[0] be null when argc is 0. */
        fprintf(stderr, "usage: %s PPPPPPPOOOOOOO\n",
                argc > 0 && argv[0] ? argv[0] : "solver");
        return 2;
    }
    uint8_t *table = build_table(&diameter);
    if (!table) {
        fputs("could not build complete state table\n", stderr);
        return 1;
    }
    const char *separator = "";
    for (uint32_t rank = rank_state(&state); rank; rank = rank_state(&state)) {
        uint8_t move = table[rank];
        printf("%s%s", separator, move_names[move]);
        separator = " ";
        state = apply_move(state, move);
    }
    putchar('\n');
    free(table);
    return output_failed();
}
