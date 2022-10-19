Caml1999N027����            /smyth/timer.mli����  /  ?  <  ������1ocaml.ppx.context��&_none_@@ �A����������)tool_name���-ppxlib_driver@@@����,include_dirs����"[]@@@����)load_path!����
%@%@@����,open_modules*����.@.@@����+for_package3����$None8@8@@����%debug=����%falseB@B@@����+use_threadsG����
K@K@@����-use_vmthreadsP����T@T@@����/recursive_typesY����]@]@@����)principalb����%f@f@@����3transparent_modulesk����.o@o@@����-unboxed_typest����7x@x@@����-unsafe_string}����@�@�@@����'cookies�����"::�����������/ppx_optcomp.env@�@@�������#env��&_none_A@ ��A@ �A��A@ ��A@ �A@@���-ocaml_version����'Defined��A@ ��A@ �A�������!4@��A@ ��A@ �A@@����"10@��#A@ ��$A@ �A@@����!0@��+A@ ��,A@ �A@@@��.A@ ��/A@ �A@@��1A@ ��2A@ �A@@@��4A@ ��5A@ �A@@@�@@�������@�@@@�@@�@@@@�@@@�@�ڠ����*ocaml.text���@@ ���@@ �A�������	A A collection of timers used to cut off program execution early. @��/smyth/timer.mliA@@�A@ F@@@@��A@@�A@ F@@���@@ ���@@ �A��
A@@�A@ F@������&Single��C H O�C H U@�����A�    �!t�� E � ��!E � �@@@��Р%Total��(F � ��)F � �@�@@��,F � ��-F � �@���)ocaml.doc��@@ ��@@ �A�������	) The timer for the total synthesis time. @��>F � ��?F � �@@@@��AF � ��BF � �@@��/@@ ��0@@ �A@�Р$Eval��KG � ��LG � �@�@@��OG � ��PG � �@���#��@@@ ��A@@ �A�������	/ The timer for live evaluation and resumption. @��`G � ��aG �@@@@��cG � ��dG �@@��Q@@ ��R@@ �A@@A@���:��W@@ ��X@@ �A�������> The available single timers. @��wD \ ^�xD \ �@@@@��zD \ ^�{D \ �@@��h@@ ��i@@ �A@���E � ���G � �@@���E � ���G � �@���Р%start���I	��I	@��@����!t���I	��I	@@���I	��I	@@@����$unit���I	��I	 @@���I	��I	 @@@���I	��I	 @@@@���{���@@ ���@@ �A�������3 Starts the timer. @���J!#��J!;@@@@���J!#��J!;@@���@@ ���@@ �A@���I	��I	 @���I	��I	 @���Р'elapsed���L=C��L=J@��@����!t���L=M��L=N@@���L=M��L=N@@@����%float���L=R��L=W@@���L=R��L=W@@@���L=M��L=W@@@@�������@@ ���@@ �A�������	= Returns how much time has elapsed since starting the timer. @���MXZ��MX�@@@@���MXZ��MX�@@���@@ ���@@ �A@��L=?�L=W@��L=?�L=W@���Р%check��O���O��@��@����!t��O���O��@@��O���O��@@@����$bool��#O���$O��@@��&O���'O��@@@��)O���*O��@@@@������@@ ��@@ �A�������	q Returns [true] if the timer is still running, and [false] if the elapsed
      time is greater than the cutoff. @��:P���;Q.@@@@��=P���>Q.@@��+@@ ��,@@ �A@��CO���DO��@��FO���GO��@@��IC H X�JR/2@@�����:@@ ��;@@ �A�������	@ A countdown timer that, once started, continues to completion. @��ZS33�[S3x@@@@��]S33�^S3x@@��K@@ ��L@@ �A@��cC H H�dR/2@��fC H H�gR/2@������%Multi��pUz��qUz�@�����A�    �!t��|W���}W��@@@��Р%Guess���X����X��@�@@���X����X��@���\��y@@ ��z@@ �A�������	% The timer for raw term enumeration. @���X����X��@@@@���X����X��@@���@@ ���@@ �A@@A@���s���@@ ���@@ �A�������= The available multi timers. @���V����V��@@@@���V����V��@@���@@ ���@@ �A@���W����X��@@���W����X��@���Р%reset���Z����Z� @��@����!t���Z���Z�@@���Z���Z�@@@����$unit���Z���Z�@@���Z���Z�@@@���Z���Z�@@@@�������@@ ���@@ �A�������3 Resets the timer. @���[��['@@@@���[��['@@���@@ ���@@ �A@���Z����Z�@���Z����Z�@���Р*accumulate��])/�])9@��@����!t��])<�])=@@��])<�])=@@@��@��@����$unit��])B� ])F@@��"])B�#])F@@@��!a��(])J�)])L@@@��+])B�,])L@@@��!a��1])Q�2])S@@@��4])A�5])S@@@��7])<�8])S@@@@�����(@@ ��)@@ �A�������	+ Accumulates additional time on the timer. @��H^TV�I^T�@@@@��K^TV�L^T�@@��9@@ ��:@@ �A@��Q])+�R])S@��T])+�U])S@���Р%check��]`���^`��@��@����!t��g`���h`��@@��j`���k`��@@@����$bool��r`���s`��@@��u`���v`��@@@��x`���y`��@@@@���L��i@@ ��j@@ �A�������	q Returns [true] if the timer is still running, and [false] if the elapsed
      time is greater than the cutoff. @���a����b�@@@@���a����b�@@��z@@ ��{@@ �A@���`����`��@���`����`��@@���Uz���c@@���l���@@ ���@@ �A�������	i A resettable countdown timer that accumulates time every time the {!accumulate}
    function is called. @���d��eq�@@@@���d��eq�@@���@@ ���@@ �A@���Uzz��c@���Uzz��c@���Р.itimer_timeout���g����g��@��@����&string���h����h��@@���h����h��@@@��@����%float���i����i��@@���i����i��@@@��@��@��!a���j����j��@@@��!b���j����j��@@@���j����j��@@@��@��!a���k����k��@@@��@��!b���l����l��@@@�����!b��m���m��@@@�����%float��m���m��@@��m���m��@@@�����$bool��m���m��@@��m���m��@@@@��m��� m��@@@��"l���#m��@@@��%k���&m��@@@��(j���)m��@@@��+i���,m��@@@��.h���/m��@@@@�����@@ �� @@ �A�������	5 A fragile hard-cutoff timer that uses Unix itimers. @��?n���@n�'@@@@��Bn���Cn�'@@��0@@ ��1@@ �A@��Hg���Im��@��Kg���Lm��@@