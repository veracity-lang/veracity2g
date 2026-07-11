SMT QUERY: (=> (and oper (and true (not (= n 0)))) (not bowtie))

(set-logic ALL)
;; BEGIN: smt_of_spec test

(declare-fun main (Int (Array Int String)) Int)
(declare-fun err () Bool)

(declare-fun j () Int)

(declare-fun i () Int)

(declare-fun arr () (Array Int Int))

(declare-fun n () Int)

(declare-fun argc () Int)

(declare-fun argv () (Array Int String))

(declare-fun realWorld_data () (Array String (Array Int String)))

(declare-fun realWorld_linenum () (Array String Int))

(declare-fun realWorld_opened () (Set String))

(define-fun states_equal
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String))
    (err_new Bool)
    (j_new Int)
    (i_new Int)
    (arr_new (Array Int Int))
    (n_new Int)
    (argc_new Int)
    (argv_new (Array Int String))
    (realWorld_data_new (Array String (Array Int String)))
    (realWorld_linenum_new (Array String Int))
    (realWorld_opened_new (Set String)) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) (and (= j j_new) (= i i_new) (= arr arr_new) (= n n_new) (= argc argc_new) (= argv argv_new) (= realWorld_data realWorld_data_new) (= realWorld_linenum realWorld_linenum_new) (= realWorld_opened realWorld_opened_new))))
)

(define-fun postcondition
  ( (i_new Int) )
  Bool
  (> i_new 0)
)

(define-fun m1_dummyMethod_1_pre_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String)) )
  Bool
  true
)

(define-fun m1_dummyMethod_1_post_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String))
    (err_new Bool)
    (j_new Int)
    (i_new Int)
    (arr_new (Array Int Int))
    (n_new Int)
    (argc_new Int)
    (argv_new (Array Int String))
    (realWorld_data_new (Array String (Array Int String)))
    (realWorld_linenum_new (Array String Int))
    (realWorld_opened_new (Set String))
    (m1_dummyMethod_1_result Bool) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) true (and (let ((realWorld_data_1 realWorld_data) (realWorld_linenum_1 realWorld_linenum) (realWorld_opened_1 realWorld_opened)) (let ((i_1 0)) (exists ((i_havoc Int)) (let ((i_2 i_havoc)) (exists ((j_havoc Int)) (let ((j_1 j_havoc)) (and (= i_2 0) (and (= j_1 0) (and (= realWorld_opened_new realWorld_opened_1) (= realWorld_linenum_new realWorld_linenum_1) (= j_new j_1) (= i_new i_2) (= realWorld_data_new realWorld_data_1)))))))))) (= arr_new arr) (= n_new n) (= argc_new argc) (= argv_new argv) (= m1_dummyMethod_1_result true))) (and (not err) err_new (not true)))
)

(define-fun m1_dummyMethod_2_pre_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String)) )
  Bool
  true
)

(define-fun m1_dummyMethod_2_post_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String))
    (err_new Bool)
    (j_new Int)
    (i_new Int)
    (arr_new (Array Int Int))
    (n_new Int)
    (argc_new Int)
    (argv_new (Array Int String))
    (realWorld_data_new (Array String (Array Int String)))
    (realWorld_linenum_new (Array String Int))
    (realWorld_opened_new (Set String))
    (m1_dummyMethod_2_result Bool) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) true (and (let ((realWorld_data_1 realWorld_data) (realWorld_linenum_1 realWorld_linenum) (realWorld_opened_1 realWorld_opened)) (and (= realWorld_opened_new realWorld_opened_1) (= realWorld_linenum_new realWorld_linenum_1) (= realWorld_data_new realWorld_data_1))) (= j_new j) (= i_new i) (= arr_new arr) (= n_new n) (= argc_new argc) (= argv_new argv) (= m1_dummyMethod_2_result true))) (and (not err) err_new (not true)))
)

(define-fun m2_dummyMethod_1_pre_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String)) )
  Bool
  true
)

(define-fun m2_dummyMethod_1_post_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String))
    (err_new Bool)
    (j_new Int)
    (i_new Int)
    (arr_new (Array Int Int))
    (n_new Int)
    (argc_new Int)
    (argv_new (Array Int String))
    (realWorld_data_new (Array String (Array Int String)))
    (realWorld_linenum_new (Array String Int))
    (realWorld_opened_new (Set String))
    (m2_dummyMethod_1_result Bool) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) true (and (let ((realWorld_data_1 realWorld_data) (realWorld_linenum_1 realWorld_linenum) (realWorld_opened_1 realWorld_opened)) (let ((i_1 0)) (exists ((i_havoc Int)) (let ((i_2 i_havoc)) (exists ((j_havoc Int)) (let ((j_1 j_havoc)) (and (= i_2 0) (and (= j_1 0) (and (= realWorld_opened_new realWorld_opened_1) (= realWorld_linenum_new realWorld_linenum_1) (= j_new j_1) (= i_new i_2) (= realWorld_data_new realWorld_data_1)))))))))) (= arr_new arr) (= n_new n) (= argc_new argc) (= argv_new argv) (= m2_dummyMethod_1_result true))) (and (not err) err_new (not true)))
)

(define-fun m2_dummyMethod_2_pre_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String)) )
  Bool
  true
)

(define-fun m2_dummyMethod_2_post_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String))
    (err_new Bool)
    (j_new Int)
    (i_new Int)
    (arr_new (Array Int Int))
    (n_new Int)
    (argc_new Int)
    (argv_new (Array Int String))
    (realWorld_data_new (Array String (Array Int String)))
    (realWorld_linenum_new (Array String Int))
    (realWorld_opened_new (Set String))
    (m2_dummyMethod_2_result Bool) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) true (and (let ((realWorld_data_1 realWorld_data) (realWorld_linenum_1 realWorld_linenum) (realWorld_opened_1 realWorld_opened)) (and (= realWorld_opened_new realWorld_opened_1) (= realWorld_linenum_new realWorld_linenum_1) (= realWorld_data_new realWorld_data_1))) (= j_new j) (= i_new i) (= arr_new arr) (= n_new n) (= argc_new argc) (= argv_new argv) (= m2_dummyMethod_2_result true))) (and (not err) err_new (not true)))
)

;; END: smt_of_spec test
(declare-fun err1 () Bool)
(declare-fun err2 () Bool)
(declare-fun err12 () Bool)
(declare-fun err21 () Bool)
(declare-fun j1 () Int)
(declare-fun j2 () Int)
(declare-fun j12 () Int)
(declare-fun j21 () Int)
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun i12 () Int)
(declare-fun i21 () Int)
(declare-fun arr1 () (Array Int Int))
(declare-fun arr2 () (Array Int Int))
(declare-fun arr12 () (Array Int Int))
(declare-fun arr21 () (Array Int Int))
(declare-fun n1 () Int)
(declare-fun n2 () Int)
(declare-fun n12 () Int)
(declare-fun n21 () Int)
(declare-fun argc1 () Int)
(declare-fun argc2 () Int)
(declare-fun argc12 () Int)
(declare-fun argc21 () Int)
(declare-fun argv1 () (Array Int String))
(declare-fun argv2 () (Array Int String))
(declare-fun argv12 () (Array Int String))
(declare-fun argv21 () (Array Int String))
(declare-fun realWorld_data1 () (Array String (Array Int String)))
(declare-fun realWorld_data2 () (Array String (Array Int String)))
(declare-fun realWorld_data12 () (Array String (Array Int String)))
(declare-fun realWorld_data21 () (Array String (Array Int String)))
(declare-fun realWorld_linenum1 () (Array String Int))
(declare-fun realWorld_linenum2 () (Array String Int))
(declare-fun realWorld_linenum12 () (Array String Int))
(declare-fun realWorld_linenum21 () (Array String Int))
(declare-fun realWorld_opened1 () (Set String))
(declare-fun realWorld_opened2 () (Set String))
(declare-fun realWorld_opened12 () (Set String))
(declare-fun realWorld_opened21 () (Set String))
(declare-fun result_0_1 () Bool)
(declare-fun result_0_21 () Bool)
(declare-fun result_0_2 () Bool)
(declare-fun result_0_12 () Bool)

(define-fun oper () Bool (and 
  (m1_dummyMethod_1_pre_condition err j i arr n argc argv realWorld_data realWorld_linenum realWorld_opened)
  (m1_dummyMethod_1_post_condition err j i arr n argc argv realWorld_data realWorld_linenum realWorld_opened err1 j1 i1 arr1 n1 argc1 argv1 realWorld_data1 realWorld_linenum1 realWorld_opened1 result_0_1)
  (m1_dummyMethod_1_pre_condition err2 j2 i2 arr2 n2 argc2 argv2 realWorld_data2 realWorld_linenum2 realWorld_opened2)
  (m1_dummyMethod_1_post_condition err2 j2 i2 arr2 n2 argc2 argv2 realWorld_data2 realWorld_linenum2 realWorld_opened2 err21 j21 i21 arr21 n21 argc21 argv21 realWorld_data21 realWorld_linenum21 realWorld_opened21 result_0_21)
  (m2_dummyMethod_2_pre_condition err j i arr n argc argv realWorld_data realWorld_linenum realWorld_opened)
  (m2_dummyMethod_2_post_condition err j i arr n argc argv realWorld_data realWorld_linenum realWorld_opened err2 j2 i2 arr2 n2 argc2 argv2 realWorld_data2 realWorld_linenum2 realWorld_opened2 result_0_2)
  (m2_dummyMethod_2_pre_condition err1 j1 i1 arr1 n1 argc1 argv1 realWorld_data1 realWorld_linenum1 realWorld_opened1)
  (m2_dummyMethod_2_post_condition err1 j1 i1 arr1 n1 argc1 argv1 realWorld_data1 realWorld_linenum1 realWorld_opened1 err12 j12 i12 arr12 n12 argc12 argv12 realWorld_data12 realWorld_linenum12 realWorld_opened12 result_0_12)
  (or (not err12) (not err21))
))

(define-fun bowtie () Bool (and
   (= result_0_1 result_0_21)
   (= result_0_2 result_0_12)
   (postcondition i12)
   (states_equal err12 j12 i12 arr12 n12 argc12 argv12 realWorld_data12 realWorld_linenum12 realWorld_opened12 err21 j21 i21 arr21 n21 argc21 argv21 realWorld_data21 realWorld_linenum21 realWorld_opened21)
))

(assert (not (=> (and oper (and true (not (= n 0)))) (not bowtie))))
(check-sat)

* * * OUT * * * 
unsat
* * * ERR * * * 

* * * * * *
SMT QUERY: (=> (and oper (and true (= n 0))) bowtie)

(set-logic ALL)
;; BEGIN: smt_of_spec test

(declare-fun main (Int (Array Int String)) Int)
(declare-fun err () Bool)

(declare-fun j () Int)

(declare-fun i () Int)

(declare-fun arr () (Array Int Int))

(declare-fun n () Int)

(declare-fun argc () Int)

(declare-fun argv () (Array Int String))

(declare-fun realWorld_data () (Array String (Array Int String)))

(declare-fun realWorld_linenum () (Array String Int))

(declare-fun realWorld_opened () (Set String))

(define-fun states_equal
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String))
    (err_new Bool)
    (j_new Int)
    (i_new Int)
    (arr_new (Array Int Int))
    (n_new Int)
    (argc_new Int)
    (argv_new (Array Int String))
    (realWorld_data_new (Array String (Array Int String)))
    (realWorld_linenum_new (Array String Int))
    (realWorld_opened_new (Set String)) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) (and (= j j_new) (= i i_new) (= arr arr_new) (= n n_new) (= argc argc_new) (= argv argv_new) (= realWorld_data realWorld_data_new) (= realWorld_linenum realWorld_linenum_new) (= realWorld_opened realWorld_opened_new))))
)

(define-fun postcondition
  ( (i_new Int) )
  Bool
  (> i_new 0)
)

(define-fun m1_dummyMethod_1_pre_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String)) )
  Bool
  true
)

(define-fun m1_dummyMethod_1_post_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String))
    (err_new Bool)
    (j_new Int)
    (i_new Int)
    (arr_new (Array Int Int))
    (n_new Int)
    (argc_new Int)
    (argv_new (Array Int String))
    (realWorld_data_new (Array String (Array Int String)))
    (realWorld_linenum_new (Array String Int))
    (realWorld_opened_new (Set String))
    (m1_dummyMethod_1_result Bool) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) true (and (let ((realWorld_data_1 realWorld_data) (realWorld_linenum_1 realWorld_linenum) (realWorld_opened_1 realWorld_opened)) (let ((i_1 0)) (exists ((i_havoc Int)) (let ((i_2 i_havoc)) (exists ((j_havoc Int)) (let ((j_1 j_havoc)) (and (= i_2 0) (and (= j_1 0) (and (= realWorld_opened_new realWorld_opened_1) (= realWorld_linenum_new realWorld_linenum_1) (= j_new j_1) (= i_new i_2) (= realWorld_data_new realWorld_data_1)))))))))) (= arr_new arr) (= n_new n) (= argc_new argc) (= argv_new argv) (= m1_dummyMethod_1_result true))) (and (not err) err_new (not true)))
)

(define-fun m1_dummyMethod_2_pre_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String)) )
  Bool
  true
)

(define-fun m1_dummyMethod_2_post_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String))
    (err_new Bool)
    (j_new Int)
    (i_new Int)
    (arr_new (Array Int Int))
    (n_new Int)
    (argc_new Int)
    (argv_new (Array Int String))
    (realWorld_data_new (Array String (Array Int String)))
    (realWorld_linenum_new (Array String Int))
    (realWorld_opened_new (Set String))
    (m1_dummyMethod_2_result Bool) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) true (and (let ((realWorld_data_1 realWorld_data) (realWorld_linenum_1 realWorld_linenum) (realWorld_opened_1 realWorld_opened)) (and (= realWorld_opened_new realWorld_opened_1) (= realWorld_linenum_new realWorld_linenum_1) (= realWorld_data_new realWorld_data_1))) (= j_new j) (= i_new i) (= arr_new arr) (= n_new n) (= argc_new argc) (= argv_new argv) (= m1_dummyMethod_2_result true))) (and (not err) err_new (not true)))
)

(define-fun m2_dummyMethod_1_pre_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String)) )
  Bool
  true
)

(define-fun m2_dummyMethod_1_post_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String))
    (err_new Bool)
    (j_new Int)
    (i_new Int)
    (arr_new (Array Int Int))
    (n_new Int)
    (argc_new Int)
    (argv_new (Array Int String))
    (realWorld_data_new (Array String (Array Int String)))
    (realWorld_linenum_new (Array String Int))
    (realWorld_opened_new (Set String))
    (m2_dummyMethod_1_result Bool) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) true (and (let ((realWorld_data_1 realWorld_data) (realWorld_linenum_1 realWorld_linenum) (realWorld_opened_1 realWorld_opened)) (let ((i_1 0)) (exists ((i_havoc Int)) (let ((i_2 i_havoc)) (exists ((j_havoc Int)) (let ((j_1 j_havoc)) (and (= i_2 0) (and (= j_1 0) (and (= realWorld_opened_new realWorld_opened_1) (= realWorld_linenum_new realWorld_linenum_1) (= j_new j_1) (= i_new i_2) (= realWorld_data_new realWorld_data_1)))))))))) (= arr_new arr) (= n_new n) (= argc_new argc) (= argv_new argv) (= m2_dummyMethod_1_result true))) (and (not err) err_new (not true)))
)

(define-fun m2_dummyMethod_2_pre_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String)) )
  Bool
  true
)

(define-fun m2_dummyMethod_2_post_condition
  ( (err Bool)
    (j Int)
    (i Int)
    (arr (Array Int Int))
    (n Int)
    (argc Int)
    (argv (Array Int String))
    (realWorld_data (Array String (Array Int String)))
    (realWorld_linenum (Array String Int))
    (realWorld_opened (Set String))
    (err_new Bool)
    (j_new Int)
    (i_new Int)
    (arr_new (Array Int Int))
    (n_new Int)
    (argc_new Int)
    (argv_new (Array Int String))
    (realWorld_data_new (Array String (Array Int String)))
    (realWorld_linenum_new (Array String Int))
    (realWorld_opened_new (Set String))
    (m2_dummyMethod_2_result Bool) )
  Bool
  (or (and err err_new) (and (not err) (not err_new) true (and (let ((realWorld_data_1 realWorld_data) (realWorld_linenum_1 realWorld_linenum) (realWorld_opened_1 realWorld_opened)) (and (= realWorld_opened_new realWorld_opened_1) (= realWorld_linenum_new realWorld_linenum_1) (= realWorld_data_new realWorld_data_1))) (= j_new j) (= i_new i) (= arr_new arr) (= n_new n) (= argc_new argc) (= argv_new argv) (= m2_dummyMethod_2_result true))) (and (not err) err_new (not true)))
)

;; END: smt_of_spec test
(declare-fun err1 () Bool)
(declare-fun err2 () Bool)
(declare-fun err12 () Bool)
(declare-fun err21 () Bool)
(declare-fun j1 () Int)
(declare-fun j2 () Int)
(declare-fun j12 () Int)
(declare-fun j21 () Int)
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun i12 () Int)
(declare-fun i21 () Int)
(declare-fun arr1 () (Array Int Int))
(declare-fun arr2 () (Array Int Int))
(declare-fun arr12 () (Array Int Int))
(declare-fun arr21 () (Array Int Int))
(declare-fun n1 () Int)
(declare-fun n2 () Int)
(declare-fun n12 () Int)
(declare-fun n21 () Int)
(declare-fun argc1 () Int)
(declare-fun argc2 () Int)
(declare-fun argc12 () Int)
(declare-fun argc21 () Int)
(declare-fun argv1 () (Array Int String))
(declare-fun argv2 () (Array Int String))
(declare-fun argv12 () (Array Int String))
(declare-fun argv21 () (Array Int String))
(declare-fun realWorld_data1 () (Array String (Array Int String)))
(declare-fun realWorld_data2 () (Array String (Array Int String)))
(declare-fun realWorld_data12 () (Array String (Array Int String)))
(declare-fun realWorld_data21 () (Array String (Array Int String)))
(declare-fun realWorld_linenum1 () (Array String Int))
(declare-fun realWorld_linenum2 () (Array String Int))
(declare-fun realWorld_linenum12 () (Array String Int))
(declare-fun realWorld_linenum21 () (Array String Int))
(declare-fun realWorld_opened1 () (Set String))
(declare-fun realWorld_opened2 () (Set String))
(declare-fun realWorld_opened12 () (Set String))
(declare-fun realWorld_opened21 () (Set String))
(declare-fun result_0_1 () Bool)
(declare-fun result_0_21 () Bool)
(declare-fun result_0_2 () Bool)
(declare-fun result_0_12 () Bool)

(define-fun oper () Bool (and 
  (m1_dummyMethod_1_pre_condition err j i arr n argc argv realWorld_data realWorld_linenum realWorld_opened)
  (m1_dummyMethod_1_post_condition err j i arr n argc argv realWorld_data realWorld_linenum realWorld_opened err1 j1 i1 arr1 n1 argc1 argv1 realWorld_data1 realWorld_linenum1 realWorld_opened1 result_0_1)
  (m1_dummyMethod_1_pre_condition err2 j2 i2 arr2 n2 argc2 argv2 realWorld_data2 realWorld_linenum2 realWorld_opened2)
  (m1_dummyMethod_1_post_condition err2 j2 i2 arr2 n2 argc2 argv2 realWorld_data2 realWorld_linenum2 realWorld_opened2 err21 j21 i21 arr21 n21 argc21 argv21 realWorld_data21 realWorld_linenum21 realWorld_opened21 result_0_21)
  (m2_dummyMethod_2_pre_condition err j i arr n argc argv realWorld_data realWorld_linenum realWorld_opened)
  (m2_dummyMethod_2_post_condition err j i arr n argc argv realWorld_data realWorld_linenum realWorld_opened err2 j2 i2 arr2 n2 argc2 argv2 realWorld_data2 realWorld_linenum2 realWorld_opened2 result_0_2)
  (m2_dummyMethod_2_pre_condition err1 j1 i1 arr1 n1 argc1 argv1 realWorld_data1 realWorld_linenum1 realWorld_opened1)
  (m2_dummyMethod_2_post_condition err1 j1 i1 arr1 n1 argc1 argv1 realWorld_data1 realWorld_linenum1 realWorld_opened1 err12 j12 i12 arr12 n12 argc12 argv12 realWorld_data12 realWorld_linenum12 realWorld_opened12 result_0_12)
  (or (not err12) (not err21))
))

(define-fun bowtie () Bool (and
   (= result_0_1 result_0_21)
   (= result_0_2 result_0_12)
   (postcondition i12)
   (states_equal err12 j12 i12 arr12 n12 argc12 argv12 realWorld_data12 realWorld_linenum12 realWorld_opened12 err21 j21 i21 arr21 n21 argc21 argv21 realWorld_data21 realWorld_linenum21 realWorld_opened21)
))

(assert (not (=> (and oper (and true (= n 0))) bowtie)))
(check-sat)

* * * OUT * * * 
sat
* * * ERR * * * 

* * * * * *
Condition at ../benchmarks/rhl/bubblesort.vcy:[6.5-20.6] verified as incorrect: n == 0
