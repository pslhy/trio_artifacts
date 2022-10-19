Caml1999N027����            2smyth/endpoint.mli����  *�     H  Ƞ����1ocaml.ppx.context��&_none_@@ �A����������)tool_name���-ppxlib_driver@@@����,include_dirs����"[]@@@����)load_path!����
%@%@@����,open_modules*����.@.@@����+for_package3����$None8@8@@����%debug=����%falseB@B@@����+use_threadsG����
K@K@@����-use_vmthreadsP����T@T@@����/recursive_typesY����]@]@@����)principalb����%f@f@@����3transparent_modulesk����.o@o@@����-unboxed_typest����7x@x@@����-unsafe_string}����@�@�@@����'cookies�����"::�����������/ppx_optcomp.env@�@@�������#env��&_none_A@ ��A@ �A��A@ ��A@ �A@@���-ocaml_version����'Defined��A@ ��A@ �A�������!4@��A@ ��A@ �A@@����"10@��#A@ ��$A@ �A@@����!0@��+A@ ��,A@ �A@@@��.A@ ��/A@ �A@@��1A@ ��2A@ �A@@@��4A@ ��5A@ �A@@@�@@�������@�@@@�@@�@@@@�@@@�@�ڠ����*ocaml.text���@@ ���@@ �A�������
  � Endpoints for clients using the {e Smyth} library.

    Two main endpoints are exposed: the {!section:solve} endpoint and the
    {!section:test} endpoint.
    A third endpoint, {!section:assertion}, is also provided for the more niche
    case of gathering information about assertions encoded in sketches.

    These endpoints take in the surface-level string representations of their
    inputs. @��2smyth/endpoint.mliA@@�I��@@@@��A@@�I��@@���@@ ���@@ �A��
A@@�I��@���A�    �%error��L���L��@@@��Р)TypeError��M���M��@����������$Lang#exp��+M���,M��@@��.M���/M��@@@������$Type%error��9M���:M�@@��<M���=M�@@@@��?M���@M�@@@@@��BM���CM�@@�Р)EvalError��IN�JN@������&string��SN�TN@@��VN�WN@@@@@��YN�ZN@@�Р(TimedOut��`O�aO'@������%float��jO+�kO0@@��mO+�nO0@@@@@��pO�qO0@@�Р+NoSolutions��wP15�xP1@@�@@��{P13�|P1@@@�Р4PartialNotSubsetFull���QAE��QAY@�@@���QAC��QAY@@@A@���)ocaml.doc��x@@ ��y@@ �A�������	0 The type of errors that clients might receive. @���K����K��@@@@���K����K��@@���@@ ���@@ �A���(deriving���RZ]��RZe@��������$show���RZf��RZj@���RZf��RZj@@@@���RZf��RZj@@���RZZ��RZk@���4���@@ ���@@ �A�������	G The given partial assertions are not a subset of the full assertions. @���Slp��Sl�@@@@���Slp��Sl�@@���@@ ���@@ �A@���L����RZk@@���L����RZk@���Р(pp_error���L����RZk@��@������4Ppx_deriving_runtime&Format)formatter���L����RZk@@���L����RZk@@@��@�������L����L��@@���L����RZk@@@�����$unit��L���RZk@@��	L���
RZk@@@��L���RZk@@@��L���RZk@@@@@��L���RZk@��L���RZk@���Р*show_error��L���RZk@��@������'L���(L��@@��*L���+RZk@@@�����G&string��3L���4RZk@@��6L���7RZk@@@��9L���:RZk@@@@@��<L���=RZk@��?L���@RZk@�����������-ocaml.warning���A@ ���A@ �A�������#-32@���A@ ���A@ �A@@@���A@ ���A@ �A@���A@ ���A@ �A��bL���cRZkA@��eL���fRZkA@��hL���iRZkA���)ocaml.doc���A@ ���A@ �A�������'@inline@���A@ ���A@ �A@@@���A@ ���A@ �A@���A@ ���A@ �A���+merlin.hide���A@ ���A@ �A�@��v@@ ��w@@ �A@���L����RZkA���A�    �(response���U����U��@����!a���U����U��@@@B@@@A�����&result���V����V��@���!a���V����V��@@@�����%error���V����V��@@���V����V��@@@@���V����V��@@@���9���@@ ���@@ �A�������	. The response type that clients will receive. @���W����W�@@@@���W����W�@@���@@ ���@@ �A@���U����V��@@���U����V��@��������@@ ���@@ �A�������1 {1:solve Solve} @���Y��Y1@@@@���Y��Y1@@���@@ ���@@ �A���Y��Y1@���A�    �,solve_result��[38�[3D@@@��Р-hole_fillings��
\GK�\GX@@����$list��\G|�\G�@�����$list��\Gw�\G{@���������$Lang)hole_name��)\G\�*\Gj@@��,\G\�-\Gj@@@������$Lang#exp��7\Gm�8\Gu@@��:\Gm�;\Gu@@@@��=\G\�>\Gu@@@@��@\G[�A\G{@@@@��C\G[�D\G�@@@��F\GK�G^��@������7@@ ��8@@ �A�������	C A list of hole fillings that satisfy the constraints of a sketch. @��W]���X]��@@@@��Z]���[]��@@��H@@ ��I@@ �A@�Р*time_taken��d^���e^��@@����%float��l^���m^��@@��o^���p^��@@@��r^���s^��@�����c@@ ��d@@ �A�������	4 The time taken to produce the valid hole fillings. @���_����_�"@@@@���_����_�"@@��t@@ ��u@@ �A@@A@�����z@@ ��{@@ �A�������	/ The result of a successful "solve" operation. @���a''��a'[@@@@���a''��a'[@@���@@ ���@@ �A@���[33��`#&@@���[33��`#&@���Р-solve_program���c]a��c]n@��@�����'Desugar'program���c]q��c]�@@���c]q��c]�@@@����(response���c]���c]�@�����,solve_result���c]���c]�@@���c]���c]�@@@@���c]���c]�@@@���c]q��c]�@@@@@���c]]��c]�@���c]]��c]�@���Р%solve���e����e��@���&sketch����&string���e����e��@@���e����e��@@@����(response���e����e��@�����,solve_result��e���e��@@��
e���e��@@@@��e���e��@@@��e���e��@@@@������@@ ��@@ �A�������	a [solve sketch] tries to return a {!solve_result} that satisfies the
    assertions in [sketch]. @��!f���"g4@@@@��$f���%g4@@��@@ ��@@ �A@��*e���+e��@��-e���.e��@�����A�� @@ ��!@@ �A�������/ {1:test Test} @��@i66�Ai6J@@@@��Ci66�Di6J@@��1@@ ��2@@ �A��Ii66�Ji6J@���A�    �+test_result��SkLQ�TkL\@@@��Р=specification_assertion_count��[l_c�\l_�@@����#int��cl_��dl_�@@��fl_��gl_�@@@��il_c�jn��@�����Z@@ ��[@@ �A�������	0 The number of assertions in the specification. @��zm���{m��@@@@��}m���~m��@@��k@@ ��l@@ �A@�Р/assertion_count���n����n��@@����#int���n����n��@@���n����n��@@@���n����p@������@@ ���@@ �A�������	) The number of assertions in the sketch. @���o����o�@@@@���o����o�@@���@@ ���@@ �A@�Р+top_success���p��p@@����$bool���p ��p$@@���p ��p$@@@���p��rad@���;���@@ ���@@ �A�������	2 Whether or not the top-ranked solution is valid. @���q%)��q%`@@@@���q%)��q%`@@���@@ ���@@ �A@�Р5top_recursive_success���rae��raz@@����$bool���ra}��ra�@@���ra}��ra�@@@���rae��t��@���g���@@ ���@@ �A�������	< Whether or not the top-ranked recursive solution is valid. @���s����s��@@@@��s���s��@@���@@ ���@@ �A@�Р*time_taken��t���t��@@����%float��t���t��@@��t���t��@@@��t���t��@������
@@ ��@@ �A�������	* The time taken to produce these results. @��*u���+u�@@@@��-u���.u�@@��@@ ��@@ �A@@A@������!@@ ��"@@ �A�������	. The result of a successful "test" operation. @��Aw�BwJ@@@@��Dw�EwJ@@��2@@ ��3@@ �A@��JkLL�Kv@@��MkLL�Nv@���Р$test��VyLP�WyLT@���-specification����&string��bzWg�czWm@@��ezWg�fzWm@@@���&sketch����&string��q{qz�r{q�@@��t{qz�u{q�@@@���(examples����&string���|����|��@@���|����|��@@@����(response���}����}��@�����+test_result���}����}��@@���}����}��@@@@���}����}��@@@���|����}��@@@���{qs��}��@@@���zWY��}��@@@@������@@ ���@@ �A�������
  = [test specification sketch examples] synthesizes hole fillings for
    [sketch] using [examples], then tests these hole fillings for validity
    against [specification].

   In typical use, [specification] and [examples] are lists of assertions, and
   [sketch] is a partially-completed program with no assertions. @���~���� C��@@@@���~���� C��@@���@@ ���@@ �A@���yLL��}��@���yLL��}��@���Р/test_assertions��� E���� E�	@���-specification����&string��� F	
	�� F	
	 @@��� F	
	�� F	
	 @@@���&sketch����&string��� G	$	-�� G	$	3@@��� G	$	-�� G	$	3@@@���*assertions����$list��� H	7	[�� H	7	_@���������$Lang#exp�� H	7	F� H	7	N@@�� H	7	F� H	7	N@@@������$Lang#exp�� H	7	Q� H	7	Y@@�� H	7	Q� H	7	Y@@@@�� H	7	F� H	7	Y@@@@�� H	7	E� H	7	_@@@����(response��  I	d	r�! I	d	z@�����+test_result��) I	d	f�* I	d	q@@��, I	d	f�- I	d	q@@@@��/ I	d	f�0 I	d	z@@@��2 H	7	9�3 I	d	z@@@��5 G	$	&�6 I	d	z@@@��8 F	
	�9 I	d	z@@@@������)@@ ��*@@ �A�������	g A convenience wrapper for {!test} that takes in a list of parsed assertions
    rather than a string. @��I J	{	{�J K	�	�@@@@��L J	{	{�M K	�	�@@��:@@ ��;@@ �A@��R E���S I	d	z@��U E���V I	d	z@�����i��H@@ ��I@@ �A�������> {1:assertion Assertion Info} @��h M	�	��i M	�
@@@@��k M	�	��l M	�
@@��Y@@ ��Z@@ �A��q M	�	��r M	�
@���Р.assertion_info��z O

�{ O

 @���-specification����&string��� P
#
3�� P
#
9@@��� P
#
3�� P
#
9@@@���*assertions����&string��� Q
=
J�� Q
=
P@@��� Q
=
J�� Q
=
P@@@����(response��� R
T
}�� R
T
�@�����$list��� R
T
x�� R
T
|@��������$bool��� R
T
W�� R
T
[@@��� R
T
W�� R
T
[@@@�����$list��� R
T
g�� R
T
k@������$Lang#exp��� R
T
^�� R
T
f@@��� R
T
^�� R
T
f@@@@��� R
T
^�� R
T
k@@@������$Lang#exp��� R
T
n�� R
T
v@@��� R
T
n�� R
T
v@@@@��� R
T
W�� R
T
v@@@@��� R
T
V�� R
T
|@@@@��� R
T
V�� R
T
�@@@��� Q
=
?�� R
T
�@@@��� P
#
%�� R
T
�@@@@���i���@@ ���@@ �A�������
  1 [assertion_info specification assertions] returns a list consisting of
    values [(included, [x0, ..., xN], y)] for each assertion in
    [specification], which should each be of the form [f x0 ... xN == y].
    [included] is true if and only if the corresponding assertion is also in
    [assertions]. @��  S
�
�� W��@@@@�� S
�
�� W��@@���@@ ���@@ �A@��	 O

�
 R
T
�@�� O

� R
T
�@@