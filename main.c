#include <stdio.h>
#include <math.h>

enum
{
    MAX_ELEM = 30
};

long double A[MAX_ELEM][MAX_ELEM]; //изначальная матрица
long double A_g1[MAX_ELEM][MAX_ELEM]; //метода Гаусса
long double A_g2[MAX_ELEM][MAX_ELEM]; //метода Гаусса с выбором главного элемента
long double A_T[MAX_ELEM][MAX_ELEM]; //транспонированная матрица
long double A_up_rel[MAX_ELEM][MAX_ELEM]; //A_T * A
long double b[MAX_ELEM]; //правая часть
long double b_g1[MAX_ELEM]; //метода Гаусса
long double b_g2[MAX_ELEM]; //метода Гаусса с выбором главного элемента
long double b_up_rel[MAX_ELEM]; //A_T * b
int x_rev[MAX_ELEM]; //перестановка решений
long double x_prev[MAX_ELEM]; //x_k
long double x_now[MAX_ELEM]; //x_{k + 1}
long double w; //\omeaga
long double eps; //\epsilon
int n, m; // порядок, параметр
int iter; // кол-во итераций
long double A_reverse[MAX_ELEM][MAX_ELEM]; // обратная матрица
long double det_A = 1; //определитель

void input_var2(void) { //формула input параметров
    while (1) {
        printf("Please enter Matrix Order\n");
        scanf("%d", &n);
        printf("and Parameter m\n");
        scanf("%d", &m);
        if (n <= 0) {
            fprintf(stderr, "incorrect input\n");
            continue;
        }
        if (m == 0) {
            fprintf(stderr, "incorrect input\n");
            continue;
        }
        if (m == -n) {
            fprintf(stderr, "incorrect input\n");
            continue;
        }
        break;
    }
}

void fill_formula(void) { //формирование СЛАУ по формуле
    for (int i = 1; i <= n; ++i) {
        for (int j = 1; j <= n; ++j) {
            A[i - 1][j - 1] = ((i == j) ? (n + m * m + ((long double)j) / m + ((long double)i) / n) : ((long double)(i + j) / (m + n)));
        }
    }

    for (int i = 1; i <= n; ++i) {
        b[i - 1] = m * i + n;
    }
}

void fill_file(void) { //формирование СЛАУ из файла
    FILE *fd_matrix, *fd_right;
    while (1) {
        char s[256];
        printf("Please enter the filename for the matrix\n");
        scanf("%s", s);
        fd_matrix = fopen(s, "r");
        if (fd_matrix == NULL) {
            fprintf(stderr, "incorrect input\n");
            continue;
        }
        break;
    }

    while (1) {
        char s[256];
        printf("Please enter the filename for the right side\n");
        scanf("%s", s);
        fd_right = fopen(s, "r");
        if (fd_right == NULL) {
            fprintf(stderr, "incorrect input\n");
            continue;
        }
        break;
    }

    int tempor_buf[MAX_ELEM * MAX_ELEM];
    n = 0;
    while (fscanf(fd_matrix, "%d", tempor_buf + n) != EOF) {
        ++n;
    }

    double n_vr = sqrt(n);
    if (n_vr == (int) n_vr) {
        n = n_vr;
    } else {
        fprintf(stderr, "incorrect input\n");
        fclose(fd_matrix);
        fclose(fd_right);
        fill_file();
    }

    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            A[i][j] = tempor_buf[n * i + j];
        }
    }

    int prav_b;

    for (int i = 0; i < n; ++i) {
        if (fscanf(fd_right, "%d", &prav_b) == EOF) {
            fprintf(stderr, "incorrect input\n");
            fclose(fd_matrix);
            fclose(fd_right);
            fill_file();
        }
        b[i] = prav_b;
    }

    fclose(fd_matrix);
    fclose(fd_right);
}

void sub_vec(long double av[MAX_ELEM], long double bv[MAX_ELEM], long double vr) { //разность векторов
    for (int i = 0; i < n; ++i) {
        bv[i] -= vr * av[i];
    }
}

void triangolize(long double At[MAX_ELEM][MAX_ELEM], long double bt[MAX_ELEM], int flag) { //приведение к треугольной форме
    for (int i = 0; i < n; ++i) {
        long double vr = At[i][i];
        bt[i] /= vr;
        for (int j = i; j < n; ++j) {
            At[i][j] /= vr;
        }
        if (flag) {
            for (int j = 0; j < n; ++j) {
                A_reverse[i][j] /= vr;
            }
        }

        for (int j = i + 1; j < n; ++j) {
            bt[j] -= At[j][i] * bt[i];
            if (flag) {
                sub_vec(A_reverse[i], A_reverse[j], At[j][i]);
            }
            sub_vec(At[i], At[j], At[j][i]);
        }
    }
}

long double abs_d(long double a) { //абсолютное значение числа типа long double
    if (a > 0) {
        return a;
    } else {
        return -a;
    }
}

int max_elem(long double av[MAX_ELEM]) { //поиск индекса с максималоьным абсолютным значением
    int ma_uk = 0;
    for (int i = 1; i < n; ++i) {
        if (abs_d(av[i]) > abs_d(av[ma_uk])) {
            ma_uk = i;
        }
    }
    return ma_uk;
}

void swap_column(long double At[MAX_ELEM][MAX_ELEM], int uk, int left) { //преставить местами столбцы
    for (int i = 0; i < n; ++i) {
        long double vr =  At[i][uk];
        At[i][uk] = At[i][left];
        At[i][left] = vr;
    }
}

void triangolize_with_melem(long double At[MAX_ELEM][MAX_ELEM], long double bt[MAX_ELEM]) { //приведение к треугольной форме с главным элементом
    int ch_nch = 0;
    for (int i = 0; i < n; ++i) {
        int uk = max_elem(At[i]);
        int vr_rev = x_rev[i];
        x_rev[i] = x_rev[uk];
        x_rev[uk] = vr_rev;
        ch_nch = (ch_nch + 1) % 2;
        swap_column(At, uk, i);

        long double vr = At[i][i];
        if (vr == 0) {
            det_A = 0;
            break;
        }
        det_A *= vr;
        bt[i] /= vr;
        for (int j = i; j < n; ++j) {
            At[i][j] /= vr;
        }

        for (int j = i + 1; j < n; ++j) {
            bt[j] -= At[j][i] * bt[i];
            sub_vec(At[i], At[j], At[j][i]);
        }
    }
    if (ch_nch) {
        det_A *= -1;
    }
}

void rever_proc(long double At[MAX_ELEM][MAX_ELEM], long double bt[MAX_ELEM], int flag) { //обратный ход
    for (int i = n - 1; i > 0; --i) {
        for (int j = i - 1; j >= 0; --j) {
            bt[j] -= At[j][i] * bt[i];
            if (flag) {
                sub_vec(A_reverse[i], A_reverse[j], At[j][i]);
            }
            sub_vec(At[i], At[j], At[j][i]);

        }
    }
}

void gauss(void) { //метод Гаусса
    triangolize(A_g1, b_g1, 1);
    rever_proc(A_g1, b_g1, 1);
}

void gauss_with_melem(void) { //метод Гаусса с главным элементом
    triangolize_with_melem(A_g2, b_g2);
    if (det_A == 0) {
        return;
    }
    rever_proc(A_g2, b_g2, 0);
}

long double matrix_norm(long double At[MAX_ELEM][MAX_ELEM]) { //бесконечная матричная норма
    long double ans = 0;
    for (int i = 0; i < n; ++i) {
        long double vr = 0;
        for (int j = 0; j < n; ++j) {
            vr += abs_d(At[i][j]);
        }
        if (vr > ans) {
            ans = vr;
        }
    }

    return ans;
}

long double cond_num(void) { //нахождение обусловленности матрицы
    long double ans = matrix_norm(A) * matrix_norm(A_reverse);
    return ans;
}

long double vector_norm(long double av[MAX_ELEM], long double bv[MAX_ELEM]) { //векторная норма
    long double ans = 0;
    for (int i = 0; i < n; ++i) {
        ans += abs_d(av[i] - bv[i]);
    }
    return ans;
}

void upper_relaxation(void) { //метод вверхней релаксации
    do {
        ++iter;
        for (int i = 0; i < n; ++i) {
            x_prev[i] = x_now[i];
        }
        for (int i = 0; i < n; ++i) {
            long double sum1 = 0, sum2 = 0;
            for (int j = 0; j < i; ++j) {
                sum1 += A_up_rel[i][j] * x_now[j];
            }
            for (int j = i; j < n; ++j) {
                sum2 += A_up_rel[i][j] * x_prev[j];
            }

            x_now[i] = x_prev[i] + w * (b_up_rel[i] - sum1 - sum2) / A_up_rel[i][i];
        }
    } while (vector_norm(x_prev, x_now) > eps / 2);
}

void matrix_transpose(long double At[MAX_ELEM][MAX_ELEM]) { //транспонирование матрицы
    for (int i = 0; i < n; ++i) {
        for (int j = i; j < n; ++j) {
            long double vr = At[i][j];
            At[i][j] = At[j][i];
            At[j][i] = vr;
        }
    }
}

void mul_matrix(long double At[MAX_ELEM][MAX_ELEM], long double Bt[MAX_ELEM][MAX_ELEM], long double Ct[MAX_ELEM][MAX_ELEM]) { //умножение матриц
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            for (int k = 0; k < n; ++k) {
                Ct[i][j] += At[i][k] * Bt[k][j];
            }
        }
    }
}

void mul_matrix_vec(long double At[MAX_ELEM][MAX_ELEM], long double Bt[MAX_ELEM], long double Ct[MAX_ELEM]) { //умножение матрицы на вектор
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            Ct[i] += At[i][j] * Bt[j];
        }
    }
}

int main (void) {
    int inp_var;
    while (1) {
        printf("You have chosen to set the elements of the system matrix and its right side in the input file (press 1),"
               " or by setting a special formula (press 2)\n");
        scanf("%d", &inp_var);
        if (inp_var == 1) {
            fill_file();
            break;
        } else if (inp_var == 2) {
            input_var2();
            fill_formula();
            break;
        } else {
            fprintf(stderr, "incorrect input\n");
        }
    }

    for (int i = 0; i < n; ++i) {
        A_reverse[i][i] = 1;
    }

    for (int i = 0; i < n; ++i) {
        x_rev[i] = i;
        for (int j = 0; j < n; ++j) {
            A_g1[i][j] = A[i][j];
            A_g2[i][j] = A[i][j];
            A_T[i][j] = A[i][j];
        }
        b_g1[i] = b[i];
        b_g2[i] = b[i];
    }

    gauss_with_melem();
    if (det_A == 0) {
        fprintf(stderr, "incorrect input: det(A) = 0\n");
        return 1;
    }

    int var_method;
    while (1) {
        printf("If you want to use the Gauss method press 1\n"
               "if you want to use the upper relaxation method press 2\n"
               "if you want to use both methods press 3\n");
        scanf("%d", &var_method);
        if (var_method < 1 || var_method > 3) {
            fprintf(stderr, "incorrect input\n");
            continue;
        }
        break;
    }

    if (var_method == 1 || var_method == 3) {
        gauss();

        printf("Gauss method:\n");
        for (int i = 0; i < n; ++i) {
            printf("x%d = %.8Lf ", i + 1, b_g1[i]);
        }
        printf("\n");

        printf("Gauss method with main elem choice:\n");
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) {
                if (x_rev[j] == i) {
                    printf("x%d = %.8Lf ", i + 1, b_g2[j]);
                }
            }
        }
        printf("\n");

        printf("Determinant: %.8Lf\n", det_A);
        printf("Inverses matrix:\n");
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) {
                printf("%.8Lf ", A_reverse[i][j]);
            }
            printf("\n");
        }
        printf("Condition number: %.8Lf\n", cond_num());
    }

    if (var_method > 1) {
        matrix_transpose(A_T);
        mul_matrix(A_T, A, A_up_rel);
        mul_matrix_vec(A_T, b, b_up_rel);

        while (1) {
            printf("Please enter Parameter for upper relaxation method\n");
            scanf("%Lf", &w);
            if (w == 0) {
                fprintf(stderr, "incorrect input\n");
            } else {
                break;
            }
        }

        while (1) {
            printf("Please enter accuracy Parameter for upper relaxation method\n");
            scanf("%Lf", &eps);
            if (eps > 0) {
                break;
            } else {
                fprintf(stderr, "incorrect input\n");
            }
        }

        upper_relaxation();

        printf("Upper relaxation method\niterations: %d\n", iter);
        for (int i = 0; i < n; ++i) {
            printf("x%d = %.8Lf ", i + 1, x_now[i]);
        }
        printf("\n");
    }

    return 0;
}
