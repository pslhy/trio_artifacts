Caml1999N027����            8collections/dynArray.mli����  ��  8  T0  Oڠ����1ocaml.ppx.context��&_none_@@ �A����������)tool_name���-ppxlib_driver@@@����,include_dirs����"[]@@@����)load_path!����
%@%@@����,open_modules*����.@.@@����+for_package3����$None8@8@@����%debug=����%falseB@B@@����+use_threadsG����
K@K@@����-use_vmthreadsP����T@T@@����/recursive_typesY����]@]@@����)principalb����%f@f@@����3transparent_modulesk����.o@o@@����-unboxed_typest����7x@x@@����-unsafe_string}����@�@�@@����'cookies�����"::�����������/ppx_optcomp.env@�@@�������#env��&_none_A@ ��A@ �A��A@ ��A@ �A@@���-ocaml_version����'Defined��A@ ��A@ �A�������!4@��A@ ��A@ �A@@����"10@��#A@ ��$A@ �A@@����!0@��+A@ ��,A@ �A@@@��.A@ ��/A@ �A@@��1A@ ��2A@ �A@@@��4A@ ��5A@ �A@@@�@@�������@�@@@�@@�@@@@�@@@�@�ڠ����*ocaml.text���@@ ���@@ �A�������
  � Dynamic arrays.

    The [DynArray] module provides arrays that automatically change their size
    as necessary.  The resizing behavior of dynamic arrays can be adapted
    through customized resizer functions, as described below.

    The interface of this module is similar to the interface of the [Array]
    module in the OCaml standard library, but some functions ({!append}, for
    example) have been changed to modify their argument in-place instead of
    returning a new copy. @��8collections/dynArray.mliA@@�J��@@@@��A@@�J��@@���@@ ���@@ �A��
A@@�J��@���A�    �!t��L���L��@����!a��L���L��@@@B@@@A@���)ocaml.doc��@@ ��@@ �A�������	: The type of resizable arrays with elements of type ['a]. @��.M���/M�9@@@@��1M���2M�9@@��@@ �� @@ �A@��7L���8L��@@��:L���;L��@���Р&length��CO;?�DO;E@��@����!t��MO;J�NO;K@���!a��TO;G�UO;I@@@@��WO;G�XO;K@@@����#int��_O;O�`O;R@@��bO;O�cO;R@@@��eO;G�fO;R@@@@���I��V@@ ��W@@ �A�������	! Returns the length of an array. @��vPSS�wPSy@@@@��yPSS�zPSy@@��g@@ ��h@@ �A@��O;;��O;R@���O;;��O;R@���Р#get���R{��R{�@��@����!t���R{���R{�@���!a���R{���R{�@@@@���R{���R{�@@@��@����#int���R{���R{�@@���R{���R{�@@@��!a���R{���R{�@@@���R{���R{�@@@���R{���R{�@@@@�������@@ ���@@ �A�������	� [get a i] returns the element with index [i] of [a].  The first element
    has index 0.

    @raise Invalid_argument if [i] is not a valid index of [a]. @���S����V�6@@@@���S����V�6@@���@@ ���@@ �A@���R{{��R{�@���R{{��R{�@���Р#set���X8<��X8?@��@����!t���X8D��X8E@���!a���X8A��X8C@@@@���X8A��X8E@@@��@����#int���X8I��X8L@@���X8I� X8L@@@��@��!a��X8P�X8R@@@����$unit��X8V�X8Z@@��X8V�X8Z@@@��X8P�X8Z@@@��X8I�X8Z@@@��X8A�X8Z@@@@������@@ ��@@ �A�������	� [set a i x] replaces the element with index [i] of [a] by the value [x].
    This function {e cannot} be used to extend an array.

    @raise Invalid_argument if [i] is not a valid index of [a]. @��,Y[[�-\�$@@@@��/Y[[�0\�$@@��@@ ��@@ �A@��5X88�6X8Z@��8X88�9X8Z@�����L��+@@ ��,@@ �A�������8 {2 Array construction} @��K^&&�L^&C@@@@��N^&&�O^&C@@��<@@ ��=@@ �A��T^&&�U^&C@���Р$make��]`EI�^`EM@��@����#int��g`EO�h`ER@@��j`EO�k`ER@@@��@��!a��r`EV�s`EX@@@����!t��z`E_�{`E`@���!a���`E\��`E^@@@@���`E\��`E`@@@���`EV��`E`@@@���`EO��`E`@@@@���n��{@@ ��|@@ �A�������	� [make n x] returns a new dynamic array of length [n] that is initialized
    with [n] copies of [x].

    @raise Invalid_argument if [n] < 0 or if [n] > [Sys.max_array_length]. @���aaa��d�@@@@���aaa��d�@@���@@ ���@@ �A@���`EE��`E`@���`EE��`E`@���Р$init���f��f"@��@����#int���f$��f'@@���f$��f'@@@��@��@����#int���f,��f/@@���f,��f/@@@��!a���f3��f5@@@���f,��f5@@@����!t���f=��f>@���!a���f:��f<@@@@���f:��f>@@@���f+��f>@@@���f$��f>@@@@���Ѱ��@@ ���@@ �A�������	� [init n f] returns a new dynamic array of length [n] where the element
    with index [i] is equal to [f i].

    @raise Invalid_argument if [n] < 0 or if [n] > [Sys.max_array_length]. @���g??��j��@@@@��g??�j��@@���@@ ���@@ �A@��f�f>@��
f�f>@���Р#sub��l �l @��@����!t��l �l @���!a��$l 	�%l @@@@��'l 	�(l @@@��@����#int��1l �2l @@��4l �5l @@@��@����#int��>l �?l @@��Al �Bl @@@����!t��Il "�Jl #@���!a��Pl �Ql !@@@@��Sl �Tl #@@@��Vl �Wl #@@@��Yl �Zl #@@@��\l 	�]l #@@@@���@��M@@ ��N@@ �A�������	� [sub a i n] returns a new dynamic array containing the elements with
    indices [i], ..., [i + n - 1] of [a].

    @raise Invalid_argument if [i] and [n] do not specify a valid subarray of
    [a]. @��mm$$�nq��@@@@��pm$$�qq��@@��^@@ ��_@@ �A@��vl  �wl #@��yl  �zl #@���Р$copy���s����s��@��@����!t���s� ��s�@���!a���s����s��@@@@���s����s�@@@����!t���s���s�	@���!a���s���s�@@@@���s���s�	@@@���s����s�	@@@@�������@@ ���@@ �A�������	O [copy a] returns a new dynamic array containing the same elements as
    [a]. @���t

��uS^@@@@���t

��uS^@@���@@ ���@@ �A@���s����s�	@���s����s�	@�����ܰ��@@ ���@@ �A�������	0 {2 Array modification with automatic resizing} @���w``��w`�@@@@���w``��w`�@@���@@ ���@@ �A���w``��w`�@���Р#add���y����y��@��@����!t���y����y��@���!a���y����y��@@@@��y���y��@@@��@��!a��	y���
y��@@@����$unit��y���y��@@��y���y��@@@��y���y��@@@��y���y��@@@@������@@ ��@@ �A�������	P [add a x] adds [x] to the end of [a].  The array is automatically
    resized. @��+z���,{�@@@@��.z���/{�@@��@@ ��@@ �A@��4y���5y��@��7y���8y��@���Р&insert��@}
�A}
@��@����!t��J}
�K}
@���!a��Q}
�R}
@@@@��T}
�U}
@@@��@����#int��^}
�_}
!@@��a}
�b}
!@@@��@��!a��i}
%�j}
'@@@����$unit��q}
+�r}
/@@��t}
+�u}
/@@@��w}
%�x}
/@@@��z}
�{}
/@@@��}}
�~}
/@@@@���a��n@@ ��o@@ �A�������	� [insert a x i] inserts [x] into the array [a] at index [i].  The array is
    automatically resized.

    @raise Invalid_argument if [i] is not a valid insertion index of [a].
    Valid insertion indices are [0 .. length a]. @���~00�� B�	@@@@���~00�� B�	@@��@@ ���@@ �A@���}

��}
/@���}

��}
/@���Р,insert_range��� D		�� D		)@��@����!t��� D		.�� D		/@���!a��� D		+�� D		-@@@@��� D		+�� D		/@@@��@����#int��� D		3�� D		6@@��� D		3�� D		6@@@��@����!t��� D		=�� D		>@���!a��� D		:�� D		<@@@@��� D		:�� D		>@@@��@����#int��� D		B�� D		E@@��� D		B�� D		E@@@��@����#int��� D		I�� D		L@@��� D		I�� D		L@@@����$unit��� D		P�� D		T@@��� D		P�� D		T@@@��  D		I� D		T@@@�� D		B� D		T@@@�� D		:� D		T@@@��	 D		3�
 D		T@@@�� D		+� D		T@@@@������@@ ���@@ �A�������
   [insert_range a1 i1 a2 i2 n] inserts the subarray [sub a2 i2 n] into the
    array [a1] at index [i1].  The array [a1] is automatically resized.

    @raise Invalid_argument if [i1] and [n] do not specify a valid subarray of
    [a1] or if [i2] is not a valid insertion index of [a2]. @�� E	U	U� I
:
x@@@@��  E	U	U�! I
:
x@@��@@ ��@@ �A@��& D		�' D		T@��) D		�* D		T@���Р&remove��2 K
z
~�3 K
z
�@��@����!t��< K
z
��= K
z
�@���!a��C K
z
��D K
z
�@@@@��F K
z
��G K
z
�@@@��@����#int��P K
z
��Q K
z
�@@��S K
z
��T K
z
�@@@����$unit��[ K
z
��\ K
z
�@@��^ K
z
��_ K
z
�@@@��a K
z
��b K
z
�@@@��d K
z
��e K
z
�@@@@���H��U@@ ��V@@ �A�������	� [remove a i] removes the element with index [i] from [a].  The array is
    automatically resized.

    @raise Invalid_argument if [i] and [n] do not specify a valid subarray of
    [a]. @��u L
�
��v PP[@@@@��x L
�
��y PP[@@��f@@ ��g@@ �A@��~ K
z
z� K
z
�@��� K
z
z�� K
z
�@���Р+remove_last��� R]a�� R]l@��@����!t��� R]q�� R]r@���!a��� R]n�� R]p@@@@��� R]n�� R]r@@@����$unit��� R]v�� R]z@@��� R]v�� R]z@@@��� R]n�� R]z@@@@�������@@ ���@@ �A�������	q [remove_last a] removes the element with index [length a - 1] from [a].
    The array is automatically resized. @��� S{{�� T��@@@@��� S{{�� T��@@���@@ ���@@ �A@��� R]]�� R]z@��� R]]�� R]z@���Р,remove_range��� V���� V�@��@����!t��� V��� V�	@���!a��� V��� V�@@@@��� V��� V�	@@@��@����#int��� V��� V�@@��� V��� V�@@@��@����#int��� V��� V�@@��  V�� V�@@@����$unit�� V��	 V�@@�� V�� V�@@@�� V�� V�@@@�� V�� V�@@@�� V�� V�@@@@������@@ ��@@ �A�������	� [remove_range a i n] removes the elements with indices [i], ..., [i + n -
    1] from [a].  The array is automatically resized.

    @raise Invalid_argument if [i] and [n] do not specify a valid subarray of
    [a]. @��% W  �& [��@@@@��( W  �) [��@@��@@ ��@@ �A@��. V���/ V�@��1 V���2 V�@���Р*remove_all��: ] �; ] @��@����!t��D ] �E ] @���!a��K ] �L ] @@@@��N ] �O ] @@@����$unit��V ] �W ] @@��Y ] �Z ] @@@��\ ] �] ] @@@@���@��M@@ ��N@@ �A�������	X [remove_all a] removes all elements from [a].  The array is automatically
    resized. @��m ^�n _kz@@@@��p ^�q _kz@@��^@@ ��_@@ �A@��v ]  �w ] @��y ]  �z ] @���Р%clear��� a|��� a|�@��@����!t��� a|��� a|�@���!a��� a|��� a|�@@@@��� a|��� a|�@@@����$unit��� a|��� a|�@@��� a|��� a|�@@@��� a|��� a|�@@@@�������@@ ���@@ �A�������	j [clear a] removes all elements from [a].  The array is automatically
    resized (same as [remove_all]). @��� b���� c�@@@@��� b���� c�@@���@@ ���@@ �A@��� a||�� a|�@��� a||�� a|�@���Р&append��� e	�� e@��@����!t��� e�� e@���!a��� e�� e@@@@��� e�� e@@@��@����!t��� e�� e@���!a��� e�� e@@@@��� e�� e@@@����$unit��� e!�� e%@@��� e!�� e%@@@��  e� e%@@@�� e� e%@@@@������@@ ���@@ �A�������	k [append a b] appends the elements of [a] to the end of [b].  The array
    [b] is automatically resized.  @�� f&&� gq�@@@@�� f&&� gq�@@��@@ ��@@ �A@�� e� e%@��  e�! e%@�����4��@@ ��@@ �A�������	3 {2 Array modification without automatic resizing} @��3 i���4 i��@@@@��6 i���7 i��@@��$@@ ��%@@ �A��< i���= i��@���Р$fill��E k���F k��@��@����!t��O k���P k��@���!a��V k���W k��@@@@��Y k���Z k��@@@��@����#int��c k���d k��@@��f k���g k��@@@��@����#int��p k���q k��@@��s k���t k��@@@��@��!a��{ k���| k��@@@����$unit��� k���� k��@@��� k���� k��@@@��� k���� k��@@@��� k���� k��@@@��� k���� k��@@@��� k���� k��@@@@���v���@@ ���@@ �A�������
   [fill a i n x] replaces the elements of the array [a] with indices [i],
    ..., [i + n - 1] by [n] copies of the value [x].  This function {e cannot}
    be used to extend an array.

    @raise Invalid_argument if [i] and [n] do not specify a valid subarray of
    [a]. @��� l���� q@@@@��� l���� q@@���@@ ���@@ �A@��� k���� k��@��� k���� k��@���Р$blit��� s�� s@��@����!t��� s!�� s"@���!a��� s�� s @@@@��� s�� s"@@@��@����#int��� s&�� s)@@��� s&�� s)@@@��@����!t��� s0�� s1@���!a��� s-�� s/@@@@��� s-�� s1@@@��@����#int��� s5�� s8@@��� s5�� s8@@@��@����#int�� s<� s?@@�� s<� s?@@@����$unit�� sC� sG@@�� sC� sG@@@�� s<� sG@@@�� s5� sG@@@�� s-� sG@@@�� s&� sG@@@��! s�" sG@@@@�����@@ ��@@ �A�������
   [blit a i b j n] replaces [n] elements of array [b] starting at index [j]
    by [n] elements of array [a] starting at index [i].

    @raise Invalid_argument if [i] and [n] do not specify a valid subarray of
    [a] or [j] and [n] do not specify a valid subarray of [b]. @��2 tHH�3 x^@@@@��5 tHH�6 x^@@��#@@ ��$@@ �A@��; s�< sG@��> s�? sG@�����R��1@@ ��2@@ �A�������/ {2 Iterators} @��Q z``�R z`t@@@@��T z``�U z`t@@��B@@ ��C@@ �A��Z z``�[ z`t@���Р$iter��c |vz�d |v~@��@��@��!a��m |v��n |v�@@@����$unit��u |v��v |v�@@��x |v��y |v�@@@��{ |v��| |v�@@@��@����!t��� |v��� |v�@���!a��� |v��� |v�@@@@��� |v��� |v�@@@����$unit��� |v��� |v�@@��� |v��� |v�@@@��� |v��� |v�@@@��� |v��� |v�@@@@�������@@ ���@@ �A�������	� [iter f a] applies the function [f] successively to all elements of [a].
    It is equal to [f a1; ..., f an)], where [a1], ..., [an] are the elements
    of the array [a]. @��� }���� 8P@@@@��� }���� 8P@@���@@ ���@@ �A@��� |vv�� |v�@��� |vv�� |v�@���Р(rev_iter��� �RV�� �R^@��@��@��!a��� �Ra�� �Rc@@@����$unit��� �Rg�� �Rk@@��� �Rg�� �Rk@@@��� �Ra�� �Rk@@@��@����!t��� �Rs�� �Rt@���!a��� �Rp�� �Rr@@@@��� �Rp�� �Rt@@@����$unit��� �Rx�� �R|@@��� �Rx�� �R|@@@��  �Rp� �R|@@@�� �R`� �R|@@@@������@@ ���@@ �A�������	� [rev_iter f a] applies the function [f] successively to all elements of
    [a] in reverse direction.  It is equal to [f an; ..., f a1)], where [a1],
    ..., [an] are the elements of the array [a]. @�� �}}� �J@@@@�� �}}� �J@@��	@@ ��	@@ �A@�� �RR� �R|@��  �RR�! �R|@���Р%iteri��) �LP�* �LU@��@��@����#int��5 �LX�6 �L[@@��8 �LX�9 �L[@@@��@��!a��@ �L_�A �La@@@����$unit��H �Le�I �Li@@��K �Le�L �Li@@@��N �L_�O �Li@@@��Q �LX�R �Li@@@��@����!t��[ �Lq�\ �Lr@���!a��b �Ln�c �Lp@@@@��e �Ln�f �Lr@@@����$unit��m �Lv�n �Lz@@��p �Lv�q �Lz@@@��s �Ln�t �Lz@@@��v �LW�w �Lz@@@@���Z��	g@@ ��	h@@ �A�������	� [iteri f a] applies the function [f] successively to all elements of [a]
    and their indices.  It is equal to [f 0 a1; ..., f (n - 1) an)], where
    [a1], ..., [an] are the elements of the array [a]. @��� �{{�� �L@@@@��� �{{�� �L@@��	x@@ ��	y@@ �A@��� �LL�� �Lz@��� �LL�� �Lz@���Р)rev_iteri��� �NR�� �N[@��@��@����#int��� �N^�� �Na@@��� �N^�� �Na@@@��@��!a��� �Ne�� �Ng@@@����$unit��� �Nk�� �No@@��� �Nk�� �No@@@��� �Ne�� �No@@@��� �N^�� �No@@@��@����!t��� �Nw�� �Nx@���!a��� �Nt�� �Nv@@@@��� �Nt�� �Nx@@@����$unit��� �N|�� �N�@@��� �N|�� �N�@@@��� �Nt�� �N�@@@��� �N]�� �N�@@@@���Ͱ�	�@@ ��	�@@ �A�������	� [rev_iteri f a] applies the function [f] successively to all elements of
    [a] in reverse direction and their indices.  It is equal to [f (n - 1) an;
    ..., f 0 a1)], where [a1], ..., [an] are the elements of the array [a]. @��� ����� �k@@@@��� ����� �k@@��	�@@ ��	�@@ �A@��	 �NN�	 �N�@��	 �NN�	 �N�@���Р)fold_left��	 �mq�	 �mz@��@��@��!a��	 �m}�	 �m@@@��@��!b��	! �m��	" �m�@@@��!a��	' �m��	( �m�@@@��	* �m��	+ �m�@@@��	- �m}�	. �m�@@@��@��!a��	5 �m��	6 �m�@@@��@����!t��	? �m��	@ �m�@���!b��	F �m��	G �m�@@@@��	I �m��	J �m�@@@��!a��	O �m��	P �m�@@@��	R �m��	S �m�@@@��	U �m��	V �m�@@@��	X �m|�	Y �m�@@@@���	<��
I@@ ��
J@@ �A�������	p [fold_left f x a] returns [f (... (f (f x a1) a2) ...) an], where [a1],
    ..., [an] are the elements of [a]. @��	i ����	j ��@@@@��	l ����	m ��@@��
Z@@ ��
[@@ �A@��	r �mm�	s �m�@��	u �mm�	v �m�@���Р*fold_right��	~ ��	 �&@��@��@��!a��	� �)�	� �+@@@��@��!b��	� �/�	� �1@@@��!b��	� �5�	� �7@@@��	� �/�	� �7@@@��	� �)�	� �7@@@��@����!t��	� �?�	� �@@���!a��	� �<�	� �>@@@@��	� �<�	� �@@@@��@��!b��	� �D�	� �F@@@��!b��	� �J�	� �L@@@��	� �D�	� �L@@@��	� �<�	� �L@@@��	� �(�	� �L@@@@���	���
�@@ ��
�@@ �A�������	q [fold_right f a x] returns [f a1 (f a2 (... (f an x) ...))], where [a1],
    ..., [an] are the elements of [a]. @��	� �MM�	� ���@@@@��	� �MM�	� ���@@��
�@@ ��
�@@ �A@��	� ��	� �L@��	� ��	� �L@���Р*fold_left2��	� ����	� ���@��@��@��!a��	� ����	� ���@@@��@��!b��	� ����
  ���@@@��@��!c��
 ����
 ���@@@��!a��
 ����
 ���@@@��
 ����
 ���@@@��
 ����
 ���@@@��
 ����
 ���@@@��@��!a��
 ����
 ���@@@��@����!t��
( ����
) ���@���!b��
/ ����
0 ���@@@@��
2 ����
3 ���@@@��@����!t��
< ���
= ��@���!c��
C ����
D �� @@@@��
F ����
G ��@@@��!a��
L ���
M ��@@@��
O ����
P ��@@@��
R ����
S ��@@@��
U ����
V ��@@@��
X ����
Y ��@@@@���
<��I@@ ��J@@ �A�������	� [fold_left2 f x a b] returns [f ( ... (f (f x a1 b1) a2 b2) ... ) an bn],
    where [a1], ..., [an] are the elements of [a], and [b1], ..., [bn] are the
    elements of [b].

    @raise Invalid_argument if the two arrays have different lengths. @��
i �		�
j ��@@@@��
l �		�
m ��@@��Z@@ ��[@@ �A@��
r ����
s ��@��
u ����
v ��@���Р+fold_right2��
~ �
�
 �@��@��@��!a��
� ��
� �@@@��@��!b��
� ��
� �!@@@��@��!c��
� �%�
� �'@@@��!c��
� �+�
� �-@@@��
� �%�
� �-@@@��
� ��
� �-@@@��
� ��
� �-@@@��@����!t��
� �5�
� �6@���!a��
� �2�
� �4@@@@��
� �2�
� �6@@@��@����!t��
� �=�
� �>@���!b��
� �:�
� �<@@@@��
� �:�
� �>@@@��@��!c��
� �B�
� �D@@@��!c��
� �H�
� �J@@@��
� �B�
� �J@@@��
� �:�
� �J@@@��
� �2�
� �J@@@��
� ��
� �J@@@@���
Ͱ��@@ ���@@ �A�������	� [fold_right2 f a b x] returns [f a1 b1 (f a2 b2 ( ... (f an bn x) ... ))],
    where [a1], ..., [an] are the elements of [a], and [b1], ..., [bn] are the
    elements of [b].

    @raise Invalid_argument if the two arrays have different lengths. @��
� �KK�
� ��G@@@@��
� �KK�
� ��G@@���@@ ���@@ �A@�� �� �J@�� �� �J@���Р#map�� �IM� �IP@��@��@��!a�� �IS� �IU@@@��!b�� �IY�  �I[@@@��" �IS�# �I[@@@��@����!t��, �Ic�- �Id@���!a��3 �I`�4 �Ib@@@@��6 �I`�7 �Id@@@����!t��> �Ik�? �Il@���!b��E �Ih�F �Ij@@@@��H �Ih�I �Il@@@��K �I`�L �Il@@@��N �IR�O �Il@@@@���2��?@@ ��@@@ �A�������	r [map f a] returns an array with elements [f a1], ..., [f an], where [a1],
    ..., [an] are the elements of [a]. @��_ �mm�` ���@@@@��b �mm�c ���@@��P@@ ��Q@@ �A@��h �II�i �Il@��k �II�l �Il@���Р$mapi��t ����u ���@��@��@����#int��� ����� ���@@��� ����� ���@@@��@��!a��� ����� ���@@@��!b��� ����� �� @@@��� ����� �� @@@��� ����� �� @@@��@����!t��� ���� ��	@���!a��� ���� ��@@@@��� ���� ��	@@@����!t��� ���� ��@���!b��� ���� ��@@@@��� ���� ��@@@��� ���� ��@@@��� ����� ��@@@@�������@@ ���@@ �A�������	} [mapi f a] returns an array with elements [f 0 a1], ..., [f (n - 1) an],
    where [a1], ..., [an] are the elements of [a]. @��� ��� �_�@@@@��� ��� �_�@@���@@ ���@@ �A@��� ����� ��@��� ����� ��@���������@@ ���@@ �A�������. {2 Scanning} @��� ����� ���@@@@��� ����� ���@@���@@ ���@@ �A��� ����� ���@���Р(is_empty�� ���� ���@��@����!t�� ���� ���@���!a�� ���� ���@@@@�� ���� ���@@@����$bool��! ����" ���@@��$ ����% ���@@@��' ����( ���@@@@�����@@ ��@@ �A�������	" Tests whether an array is empty. @��8 ����9 ���@@@@��; ����< ���@@��)@@ ��*@@ �A@��A ����B ���@��D ����E ���@���Р'for_all��M ����N ���@��@��@��!a��W ����X ���@@@����$bool��_ ���` ��@@��b ���c ��@@@��e ����f ��@@@��@����!t��o ���p ��@���!a��v ���w ��@@@@��y ���z ��@@@����$bool��� ���� ��@@��� ���� ��@@@��� ���� ��@@@��� ����� ��@@@@���n��{@@ ��|@@ �A�������	p [for_all p a] returns [true] if [p x = true] for all elements [x] of the
    array [a], and [false] otherwise. @��� ��� �f�@@@@��� ��� �f�@@���@@ ���@@ �A@��� ����� ��@��� ����� ��@���Р&exists��� ����� ���@��@��@��!a��� ����� ���@@@����$bool��� ����� ���@@��� ����� ���@@@��� ����� ���@@@��@����!t��� ����� ���@���!a��� ����� ���@@@@��� ����� ���@@@����$bool��� ����� ���@@��� ����� ���@@@��� ����� ���@@@��� ����� ���@@@@���Ѱ��@@ ���@@ �A�������	o [exists p a] returns [true] if [p x = true] for some element [x] of the
    array [a], and [false] otherwise. @��� ����� �-@@@@�� ���� �-@@���@@ ���@@ �A@�� ���� ���@��
 ���� ���@���Р(for_all2�� �/3� �/;@��@��@��!a�� �/>� �/@@@@��@��!b��% �/D�& �/F@@@����$bool��- �/J�. �/N@@��0 �/J�1 �/N@@@��3 �/D�4 �/N@@@��6 �/>�7 �/N@@@��@����!t��@ �/V�A �/W@���!a��G �/S�H �/U@@@@��J �/S�K �/W@@@��@����!t��T �/^�U �/_@���!b��[ �/[�\ �/]@@@@��^ �/[�_ �/_@@@����$bool��f �/c�g �/g@@��i �/c�j �/g@@@��l �/[�m �/g@@@��o �/S�p �/g@@@��r �/=�s �/g@@@@���V��c@@ ��d@@ �A�������	� [for_all2 p a b] returns [true] if [p x y = true] for all pairs of
    elements [x] and [y] where [x] has the same index in [a] as [y] in [b].

    @raise Invalid_argument if [a] and [b] have different lengths. @��� �hh�� ��A@@@@��� �hh�� ��A@@��t@@ ��u@@ �A@��� �//�� �/g@��� �//�� �/g@���Р'exists2��� �CG�� �CN@��@��@��!a��� �CQ�� �CS@@@��@��!b��� �CW�� �CY@@@����$bool��� �C]�� �Ca@@��� �C]�� �Ca@@@��� �CW�� �Ca@@@��� �CQ�� �Ca@@@��@����!t��� �Ci�� �Cj@���!a��� �Cf�� �Ch@@@@��� �Cf�� �Cj@@@��@����!t��� �Cq�� �Cr@���!b��� �Cn�� �Cp@@@@��� �Cn�� �Cr@@@����$bool��� �Cv�� �Cz@@��� �Cv�� �Cz@@@��� �Cn�� �Cz@@@��� �Cf�� �Cz@@@��� �CP�� �Cz@@@@���۰��@@ ���@@ �A�������	� [exists2 p a b] returns [true] if [p x y = true] for some pair of elements
    [x] and [y] where [x] has the same index in [a] as [y] in [b].

    @raise Invalid_argument if [a] and [b] have different lengths. @�� �{{�	 �S@@@@�� �{{� �S@@���@@ ���@@ �A@�� �CC� �Cz@�� �CC� �Cz@�����(��@@ ��@@ �A�������/ {2 Searching} @��' �UU�( �Ui@@@@��* �UU�+ �Ui@@��@@ ��@@ �A��0 �UU�1 �Ui@���Р%first��9 �ko�: �kt@��@����!t��C �ky�D �kz@���!a��J �kv�K �kx@@@@��M �kv�N �kz@@@����&option��U �k��V �k�@���!a��\ �k~�] �k�@@@@��_ �k~�` �k�@@@��b �kv�c �k�@@@@���F��S@@ ��T@@ �A�������	� [first a] returns [Some x] if [x] is the first element (the element with
    index 0) of [a], or [None] if the array is empty. @��s ����t ��@@@@��v ����w ��@@��d@@ ��e@@ �A@��| �kk�} �k�@�� �kk�� �k�@���Р$last��� ��� �@��@����!t��� ��� �@���!a��� ��� �@@@@��� ��� �@@@����&option��� �$�� �*@���!a��� �!�� �#@@@@��� �!�� �*@@@��� ��� �*@@@@�������@@ ���@@ �A�������	� [last a] returns [Some x] if [x] is the last element (the element with
    index [length a - 1]) of [a], or [None] if the array is empty. @��� �++�� �v�@@@@��� �++�� �v�@@���@@ ���@@ �A@��� ��� �*@��� ��� �*@��������@@ ���@@ �A�������0 {2 Conversion} @��� ����� ���@@@@��� ����� ���@@���@@ ���@@ �A��� ����� ���@���Р'to_list��� ����� ���@��@����!t��� ����� ���@���!a�� ���� ���@@@@�� ���� ���@@@����$list�� ���� ���@���!a�� ���� ���@@@@�� ���� ���@@@�� ���� ���@@@@��� ��@@ ��@@ �A�������	< [to_list a] returns a list containing the elements of [a]. @��- ����. �� 2@@@@��0 ����1 �� 2@@��@@ ��@@ �A@��6 ����7 ���@��9 ����: ���@���Р'of_list��B � 4 8�C � 4 ?@��@����$list��L � 4 D�M � 4 H@���!a��S � 4 A�T � 4 C@@@@��V � 4 A�W � 4 H@@@����!t��^ � 4 O�_ � 4 P@���!a��e � 4 L�f � 4 N@@@@��h � 4 L�i � 4 P@@@��k � 4 A�l � 4 P@@@@���O��\@@ ��]@@ �A�������	E [of_list l] returns a dynamic array containing the elements of [l]. @��| � Q Q�} � Q �@@@@�� � Q Q�� � Q �@@��m@@ ��n@@ �A@��� � 4 4�� � 4 P@��� � 4 4�� � 4 P@���Р(to_array��� � � ��� � � �@��@����!t��� � � ��� � � �@���!a��� � � ��� � � �@@@@��� � � ��� � � �@@@����%array��� � � ��� � � �@���!a��� � � ��� � � �@@@@��� � � ��� � � �@@@��� � � ��� � � �@@@@�������@@ ���@@ �A�������	Z [to_array a] returns a new standard OCaml array containing the same
    elements as [a]. @��� � � ��� �!!@@@@��� � � ��� �!!@@���@@ ���@@ �A@��� � � ��� � � �@��� � � ��� � � �@���Р(of_array��� �!!!�� �!!)@��@����%array��� �!!.�� �!!3@���!a��� �!!+�� �!!-@@@@��� �!!+�� �!!3@@@����!t��� �!!:�� �!!;@���!a�� �!!7� �!!9@@@@�� �!!7� �!!;@@@��	 �!!+�
 �!!;@@@@�������@@ ���@@ �A�������	S [of_array a] returns a new dynamic array containing the same elements as
    [a]. @�� �!<!<� �!�!�@@@@�� �!<!<� �!�!�@@��@@ ��@@ �A@��# �!!�$ �!!;@��& �!!�' �!!;@�����:��@@ ��@@ �A�������
  y {2 Resizer functions}

    A resizer is a function that computes how much space is to be reserved
    when elements are added to or removed from a dynamic array.  When a
    dynamic array is created, a default resizer is assigned to it, which can
    then be changed.  When a dynamic array is copied using the functions
    [sub], [copy], or [map], the new array uses the same resizer as the
    original array.

    A resizer is called with three arguments: the current reserved size of the
    array, the number of elements of the array before the modification, and
    the number of elements of the array after the modification. @��9 �!�!��: �#�$@@@@��< �!�!��= �#�$@@��*@@ ��+@@ �A��B �!�!��C �#�$@���A�    �'resizer��L �$$�M �$$"@@@@A���@����#int��W �$$%�X �$$(@@��Z �$$%�[ �$$(@@@��@����#int��d �$$,�e �$$/@@��g �$$,�h �$$/@@@��@����#int��q �$$3�r �$$6@@��t �$$3�u �$$6@@@����#int��| �$$:�} �$$=@@�� �$$:�� �$$=@@@��� �$$3�� �$$=@@@��� �$$,�� �$$=@@@��� �$$%�� �$$=@@@���l��y@@ ��z@@ �A�������	Y The type of resizer functions. Parameters are the current size, old length, new length. @��� �$>$>�� �$>$�@@@@��� �$>$>�� �$>$�@@���@@ ���@@ �A@��� �$$�� �$$=@@��� �$$�� �$$=@���Р?doubling_resizer_with_shrinking��� �$�$��� �$�$�@����'resizer��� �$�$��� �$�$�@@��� �$�$��� �$�$�@@@@�������@@ ���@@ �A�������	j A resizer that grows and shrinks an array by doubling or halving the size
    of the array as necessary. @��� �$�$��� �%%:@@@@��� �$�$��� �%%:@@���@@ ���@@ �A@��� �$�$��� �$�$�@��� �$�$��� �$�$�@���Р	"doubling_resizer_without_shrinking��� �%<%@�� �%<%b@����'resizer��� �%<%d�� �%<%k@@��� �%<%d�� �%<%k@@@@���ΰ��@@ ���@@ �A�������	� A resizer that grows an array by doubling the size of the array as
    necessary.  It never shrinks the array, which is not a problem in many use
    cases.  This is currently the default resizer. @��� �%l%l�� �&&7@@@@��� �%l%l�� �&&7@@���@@ ���@@ �A@�� �%<%<� �%<%k@�� �%<%<� �%<%k@���Р+set_resizer�� �&9&=� �&9&H@��@����!t�� �&9&M� �&9&N@���!a��! �&9&J�" �&9&L@@@@��$ �&9&J�% �&9&N@@@��@����'resizer��. �&9&R�/ �&9&Y@@��1 �&9&R�2 �&9&Y@@@����$unit��9 �&9&]�: �&9&a@@��< �&9&]�= �&9&a@@@��? �&9&R�@ �&9&a@@@��B �&9&J�C �&9&a@@@@���&��3@@ ��4@@ �A�������	( Sets the resizer function of an array. @��S �&b&b�T �&b&�@@@@��V �&b&b�W �&b&�@@��D@@ ��E@@ �A@��\ �&9&9�] �&9&a@��_ �&9&9�` �&9&a@���Р3set_default_resizer��h �&�&��i �&�&�@��@����'resizer��r �&�&��s �&�&�@@��u �&�&��v �&�&�@@@����$unit��} �&�&��~ �&�&�@@��� �&�&��� �&�&�@@@��� �&�&��� �&�&�@@@@���g��t@@ ��u@@ �A�������	% Sets the default resizer function.  @��� �&�&��� �&�&�@@@@��� �&�&��� �&�&�@@���@@ ���@@ �A@��� �&�&��� �&�&�@��� �&�&��� �&�&�@���������@@ ���@@ �A�������"/*@��� &�&��� &�&�@@@@��� &�&��� &�&�@@���@@ ���@@ �A��� &�&��� &�&�@���Р*unsafe_get���&�&���&�&�@��@����!t���&�'��&�'@���!a���&�&���&�'@@@@���&�&���&�'@@@��@����#int���&�'��&�'
@@���&�'��&�'
@@@��!a���&�'��&�'@@@���&�'��&�'@@@���&�&���&�'@@@@@���&�&���&�'@���&�&���&�'@���Р*unsafe_set��''�'' @��@����!t��''%�''&@���!a��''"�''$@@@@��''"�''&@@@��@����#int��''*� ''-@@��"''*�#''-@@@��@��!a��*''1�+''3@@@����$unit��2''7�3'';@@��5''7�6'';@@@��8''1�9'';@@@��;''*�<'';@@@��>''"�?'';@@@@@��A''�B'';@��D''�E'';@@