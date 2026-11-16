import PlattAssemblyKernel
import PlattCertificates.Count131072.C016848
import PlattCertificates.Count131072.C016849
import PlattCertificates.Count131072.C016850
import PlattCertificates.Count131072.C016851
import PlattCertificates.Count131072.C016852
import PlattCertificates.Count131072.C016853
import PlattCertificates.Count131072.C016854
import PlattCertificates.Count131072.C016855
import PlattCertificates.Count131072.C016856
import PlattCertificates.Count131072.C016857
import PlattCertificates.Count131072.C016858
import PlattCertificates.Count131072.C016859
import PlattCertificates.Count131072.C016860
import PlattCertificates.Count131072.C016861
import PlattCertificates.Count131072.C016862
import PlattCertificates.Count131072.C016863
import PlattCertificates.Count131072.C016864
import PlattCertificates.Count131072.C016865
import PlattCertificates.Count131072.C016866
import PlattCertificates.Count131072.C016867
import PlattCertificates.Count131072.C016868
import PlattCertificates.Count131072.C016869
import PlattCertificates.Count131072.C016870
import PlattCertificates.Count131072.C016871
import PlattCertificates.Count131072.C016872
import PlattCertificates.Count131072.C016873
import PlattCertificates.Count131072.C016874
import PlattCertificates.Count131072.C016875
import PlattCertificates.Count131072.C016876
import PlattCertificates.Count131072.C016877
import PlattCertificates.Count131072.C016878
import PlattCertificates.Count131072.C016879
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000214
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16848 : List PrefixCut := [⟨56,341877676,341877894⟩,
⟨124,758684273,758684756⟩,
⟨128,785020514,785021013⟩]
theorem checked16848 : checkPrefixCuts (2^48) 2212233217 9 Manual.Count131072.C016848.packed 128 cuts16848 = true := by
 decide +kernel
def pointBounds16848 : List (Nat × Nat × Nat) := [(2212290560,97790130696620,97790509713552),(2212360192,97790547503217,97790926520414)]
theorem point_links_checked16848 : (cuts16848.take 2).map (fun c => (2212233217-1+2*2^9*c.k,97789788818944+c.lower,97790167835658+c.upper)) = pointBounds16848 := by
 decide +kernel
def cuts16849 : List PrefixCut := [⟨64,388421634,388421883⟩,
⟨128,777213411,777213907⟩]
theorem checked16849 : checkPrefixCuts (2^48) 2212364289 9 Manual.Count131072.C016849.packed 128 cuts16849 = true := by
 decide +kernel
def pointBounds16849 : List (Nat × Nat × Nat) := [(2212429824,97790962261092,97791341278554)]
theorem point_links_checked16849 : (cuts16849.take 1).map (fun c => (2212364289-1+2*2^9*c.k,97790573839458+c.lower,97790952856671+c.upper)) = pointBounds16849 := by
 decide +kernel
def cuts16850 : List PrefixCut := [⟨4,24171882,24171897⟩,
⟨72,437376985,437377261⟩,
⟨128,774114229,774114715⟩]
theorem checked16850 : checkPrefixCuts (2^48) 2212495361 9 Manual.Count131072.C016850.packed 128 cuts16850 = true := by
 decide +kernel
def pointBounds16850 : List (Nat × Nat × Nat) := [(2212499456,97791375224751,97791754242475),(2212569088,97791788429854,97792167447839)]
theorem point_links_checked16850 : (cuts16850.take 2).map (fun c => (2212495361-1+2*2^9*c.k,97791351052869+c.lower,97791730070578+c.upper)) = pointBounds16850 := by
 decide +kernel
def cuts16851 : List PrefixCut := [⟨12,73274500,73274544⟩,
⟨80,492305348,492305656⟩,
⟨128,790605503,790605999⟩]
theorem checked16851 : checkPrefixCuts (2^48) 2212626433 9 Manual.Count131072.C016851.packed 128 cuts16851 = true := by
 decide +kernel
def pointBounds16851 : List (Nat × Nat × Nat) := [(2212638720,97792198441598,97792577459837),(2212708352,97792617472446,97792996490949)]
theorem point_links_checked16851 : (cuts16851.take 2).map (fun c => (2212626433-1+2*2^9*c.k,97792125167098+c.lower,97792504185293+c.upper)) = pointBounds16851 := by
 decide +kernel
def cuts16852 : List PrefixCut := [⟨20,121735090,121735165⟩,
⟨88,540485026,540485367⟩,
⟨128,785724906,785725400⟩]
theorem checked16852 : checkPrefixCuts (2^48) 2212757505 9 Manual.Count131072.C016852.packed 128 cuts16852 = true := by
 decide +kernel
def pointBounds16852 : List (Nat × Nat × Nat) := [(2212777984,97793037507691,97793416526457),(2212847616,97793456257627,97793835276659)]
theorem point_links_checked16852 : (cuts16852.take 2).map (fun c => (2212757505-1+2*2^9*c.k,97792915772601+c.lower,97793294791292+c.upper)) = pointBounds16852 := by
 decide +kernel
def cuts16853 : List PrefixCut := [⟨28,165483444,165483548⟩,
⟨96,581917559,581917931⟩,
⟨128,775757196,775757686⟩]
theorem checked16853 : checkPrefixCuts (2^48) 2212888577 9 Manual.Count131072.C016853.packed 128 cuts16853 = true := by
 decide +kernel
def pointBounds16853 : List (Nat × Nat × Nat) := [(2212917248,97793866980951,97794246000240),(2212986880,97794283415066,97794662434623)]
theorem point_links_checked16853 : (cuts16853.take 2).map (fun c => (2212888577-1+2*2^9*c.k,97793701497507+c.lower,97794080516692+c.upper)) = pointBounds16853 := by
 decide +kernel
def cuts16854 : List PrefixCut := [⟨36,214695654,214695784⟩,
⟨104,627415164,627415555⟩,
⟨128,774439394,774439877⟩]
theorem checked16854 : checkPrefixCuts (2^48) 2213019649 9 Manual.Count131072.C016854.packed 128 cuts16854 = true := by
 decide +kernel
def pointBounds16854 : List (Nat × Nat × Nat) := [(2213056512,97794691950357,97795070970162),(2213126144,97795104669867,97795483689933)]
theorem point_links_checked16854 : (cuts16854.take 2).map (fun c => (2213019649-1+2*2^9*c.k,97794477254703+c.lower,97794856274378+c.upper)) = pointBounds16854 := by
 decide +kernel
def cuts16855 : List PrefixCut := [⟨44,265936746,265936909⟩,
⟨112,686896879,686897309⟩,
⟨128,778717825,778718314⟩]
theorem checked16855 : checkPrefixCuts (2^48) 2213150721 9 Manual.Count131072.C016855.packed 128 cuts16855 = true := by
 decide +kernel
def pointBounds16855 : List (Nat × Nat × Nat) := [(2213195776,97795517630843,97795896651164),(2213265408,97795938590976,97796317611564)]
theorem point_links_checked16855 : (cuts16855.take 2).map (fun c => (2213150721-1+2*2^9*c.k,97795251694097+c.lower,97795630714255+c.upper)) = pointBounds16855 := by
 decide +kernel
def cuts16856 : List PrefixCut := [⟨52,309668257,309668455⟩,
⟨120,722463091,722463547⟩,
⟨128,773584653,773585141⟩]
theorem checked16856 : checkPrefixCuts (2^48) 2213281793 9 Manual.Count131072.C016856.packed 128 cuts16856 = true := by
 decide +kernel
def pointBounds16856 : List (Nat × Nat × Nat) := [(2213335040,97796340080179,97796719101024),(2213404672,97796752875013,97797131896116)]
theorem point_links_checked16856 : (cuts16856.take 2).map (fun c => (2213281793-1+2*2^9*c.k,97796030411922+c.lower,97796409432569+c.upper)) = pointBounds16856 := by
 decide +kernel
def cuts16857 : List PrefixCut := [⟨60,363440612,363440842⟩,
⟨128,773666242,773666733⟩]
theorem checked16857 : checkPrefixCuts (2^48) 2213412865 9 Manual.Count131072.C016857.packed 128 cuts16857 = true := by
 decide +kernel
def pointBounds16857 : List (Nat × Nat × Nat) := [(2213474304,97797167437187,97797546458552),(2213543936,97797577662817,97797956684443)]
theorem point_links_checked16857 : (cuts16857.take 2).map (fun c => (2213412865-1+2*2^9*c.k,97796803996575+c.lower,97797183017710+c.upper)) = pointBounds16857 := by
 decide +kernel
def cuts16858 : List PrefixCut := [⟨68,407288076,407288334⟩,
⟨128,771712872,771713360⟩]
theorem checked16858 : checkPrefixCuts (2^48) 2213543937 9 Manual.Count131072.C016858.packed 128 cuts16858 = true := by
 decide +kernel
def pointBounds16858 : List (Nat × Nat × Nat) := [(2213613568,97797984950893,97798363972777)]
theorem point_links_checked16858 : (cuts16858.take 1).map (fun c => (2213543937-1+2*2^9*c.k,97797577662817+c.lower,97797956684443+c.upper)) = pointBounds16858 := by
 decide +kernel
def cuts16859 : List PrefixCut := [⟨8,46537825,46537856⟩,
⟨76,462192064,462192353⟩,
⟨128,774973166,774973650⟩]
theorem checked16859 : checkPrefixCuts (2^48) 2213675009 9 Manual.Count131072.C016859.packed 128 cuts16859 = true := by
 decide +kernel
def pointBounds16859 : List (Nat × Nat × Nat) := [(2213683200,97798395913514,97798774935659),(2213752832,97798811567753,97799190590156)]
theorem point_links_checked16859 : (cuts16859.take 2).map (fun c => (2213675009-1+2*2^9*c.k,97798349375689+c.lower,97798728397803+c.upper)) = pointBounds16859 := by
 decide +kernel
def cuts16860 : List PrefixCut := [⟨16,99427205,99427268⟩,
⟨84,508698259,508698575⟩,
⟨128,770604573,770605053⟩]
theorem checked16860 : checkPrefixCuts (2^48) 2213806081 9 Manual.Count131072.C016860.packed 128 cuts16860 = true := by
 decide +kernel
def pointBounds16860 : List (Nat × Nat × Nat) := [(2213822464,97799223776060,97799602798721),(2213892096,97799633047114,97800012070028)]
theorem point_links_checked16860 : (cuts16860.take 2).map (fun c => (2213806081-1+2*2^9*c.k,97799124348855+c.lower,97799503371453+c.upper)) = pointBounds16860 := by
 decide +kernel
def cuts16861 : List PrefixCut := [⟨24,140994933,140995023⟩,
⟨92,543247838,543248177⟩,
⟨128,758989564,758990036⟩]
theorem checked16861 : checkPrefixCuts (2^48) 2213937153 9 Manual.Count131072.C016861.packed 128 cuts16861 = true := by
 decide +kernel
def pointBounds16861 : List (Nat × Nat × Nat) := [(2213961728,97800035948361,97800414971529),(2214031360,97800438201266,97800817224683)]
theorem point_links_checked16861 : (cuts16861.take 2).map (fun c => (2213937153-1+2*2^9*c.k,97799894953428+c.lower,97800273976506+c.upper)) = pointBounds16861 := by
 decide +kernel
def cuts16862 : List PrefixCut := [⟨32,194380599,194380721⟩,
⟨100,602328854,602329236⟩,
⟨128,768987725,768988211⟩]
theorem checked16862 : checkPrefixCuts (2^48) 2214068225 9 Manual.Count131072.C016862.packed 128 cuts16862 = true := by
 decide +kernel
def pointBounds16862 : List (Nat × Nat × Nat) := [(2214100992,97800848323591,97801227347263),(2214170624,97801256271846,97801635295778)]
theorem point_links_checked16862 : (cuts16862.take 2).map (fun c => (2214068225-1+2*2^9*c.k,97800653942992+c.lower,97801032966542+c.upper)) = pointBounds16862 := by
 decide +kernel
def cuts16863 : List PrefixCut := [⟨40,236700191,236700338⟩,
⟨108,650088873,650089276⟩,
⟨128,772119957,772120439⟩]
theorem checked16863 : checkPrefixCuts (2^48) 2214199297 9 Manual.Count131072.C016863.packed 128 cuts16863 = true := by
 decide +kernel
def pointBounds16863 : List (Nat × Nat × Nat) := [(2214240256,97801659630908,97802038655091),(2214309888,97802073019590,97802452044029)]
theorem point_links_checked16863 : (cuts16863.take 2).map (fun c => (2214199297-1+2*2^9*c.k,97801422930717+c.lower,97801801954753+c.upper)) = pointBounds16863 := by
 decide +kernel
def cuts16864 : List PrefixCut := [⟨48,290581943,290582123⟩,
⟨116,706486869,706487311⟩,
⟨128,778175756,778176245⟩]
theorem checked16864 : checkPrefixCuts (2^48) 2214330369 9 Manual.Count131072.C016864.packed 128 cuts16864 = true := by
 decide +kernel
def pointBounds16864 : List (Nat × Nat × Nat) := [(2214379520,97802485632617,97802864657315),(2214449152,97802901537543,97803280562503)]
theorem point_links_checked16864 : (cuts16864.take 2).map (fun c => (2214330369-1+2*2^9*c.k,97802195050674+c.lower,97802574075192+c.upper)) = pointBounds16864 := by
 decide +kernel
def cuts16865 : List PrefixCut := [⟨56,333907369,333907576⟩,
⟨124,743558106,743558571⟩,
⟨128,771011749,771012231⟩]
theorem checked16865 : checkPrefixCuts (2^48) 2214461441 9 Manual.Count131072.C016865.packed 128 cuts16865 = true := by
 decide +kernel
def pointBounds16865 : List (Nat × Nat × Nat) := [(2214518784,97803307133799,97803686159013),(2214588416,97803716784536,97804095810008)]
theorem point_links_checked16865 : (cuts16865.take 2).map (fun c => (2214461441-1+2*2^9*c.k,97802973226430+c.lower,97803352251437+c.upper)) = pointBounds16865 := by
 decide +kernel
def cuts16866 : List PrefixCut := [⟨64,380786230,380786472⟩,
⟨128,764992736,764993222⟩]
theorem checked16866 : checkPrefixCuts (2^48) 2214592513 9 Manual.Count131072.C016866.packed 128 cuts16866 = true := by
 decide +kernel
def pointBounds16866 : List (Nat × Nat × Nat) := [(2214658048,97804125024409,97804504050140)]
theorem point_links_checked16866 : (cuts16866.take 1).map (fun c => (2214592513-1+2*2^9*c.k,97803744238179+c.lower,97804123263668+c.upper)) = pointBounds16866 := by
 decide +kernel
def cuts16867 : List PrefixCut := [⟨4,23512101,23512116⟩,
⟨72,438589116,438589393⟩,
⟨128,777148028,777148519⟩]
theorem checked16867 : checkPrefixCuts (2^48) 2214723585 9 Manual.Count131072.C016867.packed 128 cuts16867 = true := by
 decide +kernel
def pointBounds16867 : List (Nat × Nat × Nat) := [(2214727680,97804532743016,97804911769006),(2214797312,97804947820031,97805326846283)]
theorem point_links_checked16867 : (cuts16867.take 2).map (fun c => (2214723585-1+2*2^9*c.k,97804509230915+c.lower,97804888256890+c.upper)) = pointBounds16867 := by
 decide +kernel
def cuts16868 : List PrefixCut := [⟨12,70532005,70532048⟩,
⟨80,481135097,481135402⟩,
⟨128,773416637,773417123⟩]
theorem checked16868 : checkPrefixCuts (2^48) 2214854657 9 Manual.Count131072.C016868.packed 128 cuts16868 = true := by
 decide +kernel
def pointBounds16868 : List (Nat × Nat × Nat) := [(2214866944,97805356910948,97805735937457),(2214936576,97805767514040,97806146540811)]
theorem point_links_checked16868 : (cuts16868.take 2).map (fun c => (2214854657-1+2*2^9*c.k,97805286378943+c.lower,97805665405409+c.upper)) = pointBounds16868 := by
 decide +kernel
def cuts16869 : List PrefixCut := [⟨20,122375092,122375171⟩,
⟨88,530029564,530029894⟩,
⟨128,775022768,775023252⟩]
theorem checked16869 : checkPrefixCuts (2^48) 2214985729 9 Manual.Count131072.C016869.packed 128 cuts16869 = true := by
 decide +kernel
def pointBounds16869 : List (Nat × Nat × Nat) := [(2215006208,97806182170672,97806561197703),(2215075840,97806589825144,97806968852426)]
theorem point_links_checked16869 : (cuts16869.take 2).map (fun c => (2214985729-1+2*2^9*c.k,97806059795580+c.lower,97806438822532+c.upper)) = pointBounds16869 := by
 decide +kernel
def cuts16870 : List PrefixCut := [⟨28,165952364,165952470⟩,
⟨96,568625684,568626039⟩,
⟨128,759474954,759475429⟩]
theorem checked16870 : checkPrefixCuts (2^48) 2215116801 9 Manual.Count131072.C016870.packed 128 cuts16870 = true := by
 decide +kernel
def pointBounds16870 : List (Nat × Nat × Nat) := [(2215145472,97807000770712,97807379798254),(2215215104,97807403444032,97807782471823)]
theorem point_links_checked16870 : (cuts16870.take 2).map (fun c => (2215116801-1+2*2^9*c.k,97806834818348+c.lower,97807213845784+c.upper)) = pointBounds16870 := by
 decide +kernel
def cuts16871 : List PrefixCut := [⟨36,218418611,218418746⟩,
⟨104,623988886,623989276⟩,
⟨128,768832325,768832802⟩]
theorem checked16871 : checkPrefixCuts (2^48) 2215247873 9 Manual.Count131072.C016871.packed 128 cuts16871 = true := by
 decide +kernel
def pointBounds16871 : List (Nat × Nat × Nat) := [(2215284736,97807812711913,97808191739959),(2215354368,97808218282188,97808597310489)]
theorem point_links_checked16871 : (cuts16871.take 2).map (fun c => (2215247873-1+2*2^9*c.k,97807594293302+c.lower,97807973321213+c.upper)) = pointBounds16871 := by
 decide +kernel
def cuts16872 : List PrefixCut := [⟨44,266177474,266177639⟩,
⟨112,683665084,683665504⟩,
⟨128,775647779,775648258⟩]
theorem checked16872 : checkPrefixCuts (2^48) 2215378945 9 Manual.Count131072.C016872.packed 128 cuts16872 = true := by
 decide +kernel
def pointBounds16872 : List (Nat × Nat × Nat) := [(2215424000,97808629303101,97809008331654),(2215493632,97809046790711,97809425819519)]
theorem point_links_checked16872 : (cuts16872.take 2).map (fun c => (2215378945-1+2*2^9*c.k,97808363125627+c.lower,97808742154015+c.upper)) = pointBounds16872 := by
 decide +kernel
def cuts16873 : List PrefixCut := [⟨52,316217288,316217487⟩,
⟨120,728978014,728978470⟩,
⟨128,777888475,777888961⟩]
theorem checked16873 : checkPrefixCuts (2^48) 2215510017 9 Manual.Count131072.C016873.packed 128 cuts16873 = true := by
 decide +kernel
def pointBounds16873 : List (Nat × Nat × Nat) := [(2215563264,97809454990694,97809834019760),(2215632896,97809867751420,97810246780743)]
theorem point_links_checked16873 : (cuts16873.take 2).map (fun c => (2215510017-1+2*2^9*c.k,97809138773406+c.lower,97809517802273+c.upper)) = pointBounds16873 := by
 decide +kernel
def cuts16874 : List PrefixCut := [⟨60,362312823,362313053⟩,
⟨128,767806605,767807091⟩]
theorem checked16874 : checkPrefixCuts (2^48) 2215641089 9 Manual.Count131072.C016874.packed 128 cuts16874 = true := by
 decide +kernel
def pointBounds16874 : List (Nat × Nat × Nat) := [(2215702528,97810278974704,97810658004287),(2215772160,97810684468486,97811063498325)]
theorem point_links_checked16874 : (cuts16874.take 2).map (fun c => (2215641089-1+2*2^9*c.k,97809916661881+c.lower,97810295691234+c.upper)) = pointBounds16874 := by
 decide +kernel
def cuts16875 : List PrefixCut := [⟨68,411705658,411705915⟩,
⟨128,766999251,766999735⟩]
theorem checked16875 : checkPrefixCuts (2^48) 2215772161 9 Manual.Count131072.C016875.packed 128 cuts16875 = true := by
 decide +kernel
def pointBounds16875 : List (Nat × Nat × Nat) := [(2215841792,97811096174144,97811475204240)]
theorem point_links_checked16875 : (cuts16875.take 1).map (fun c => (2215772161-1+2*2^9*c.k,97810684468486+c.lower,97811063498325+c.upper)) = pointBounds16875 := by
 decide +kernel
def cuts16876 : List PrefixCut := [⟨8,46999127,46999157⟩,
⟨76,453978974,453979259⟩,
⟨128,769747983,769748461⟩]
theorem checked16876 : checkPrefixCuts (2^48) 2215903233 9 Manual.Count131072.C016876.packed 128 cuts16876 = true := by
 decide +kernel
def pointBounds16876 : List (Nat × Nat × Nat) := [(2215911424,97811498466864,97811877497217),(2215981056,97811905446711,97812284477319)]
theorem point_links_checked16876 : (cuts16876.take 2).map (fun c => (2215903233-1+2*2^9*c.k,97811451467737+c.lower,97811830498060+c.upper)) = pointBounds16876 := by
 decide +kernel
def cuts16877 : List PrefixCut := [⟨16,97167942,97168004⟩,
⟨84,514283324,514283641⟩,
⟨128,779990679,779991158⟩]
theorem checked16877 : checkPrefixCuts (2^48) 2216034305 9 Manual.Count131072.C016877.packed 128 cuts16877 = true := by
 decide +kernel
def pointBounds16877 : List (Nat × Nat × Nat) := [(2216050688,97812318383662,97812697414525),(2216120320,97812735499044,97813114530162)]
theorem point_links_checked16877 : (cuts16877.take 2).map (fun c => (2216034305-1+2*2^9*c.k,97812221215720+c.lower,97812600246521+c.upper)) = pointBounds16877 := by
 decide +kernel
def cuts16878 : List PrefixCut := [⟨24,143774370,143774461⟩,
⟨92,559339509,559339858⟩,
⟨128,780071428,780071919⟩]
theorem checked16878 : checkPrefixCuts (2^48) 2216165377 9 Manual.Count131072.C016878.packed 128 cuts16878 = true := by
 decide +kernel
def pointBounds16878 : List (Nat × Nat × Nat) := [(2216189952,97813144980769,97813524012140),(2216259584,97813560545908,97813939577537)]
theorem point_links_checked16878 : (cuts16878.take 2).map (fun c => (2216165377-1+2*2^9*c.k,97813001206399+c.lower,97813380237679+c.upper)) = pointBounds16878 := by
 decide +kernel
def cuts16879 : List PrefixCut := [⟨32,197868221,197868345⟩,
⟨100,613407286,613407665⟩,
⟨128,787645339,787645825⟩]
theorem checked16879 : checkPrefixCuts (2^48) 2216296449 9 Manual.Count131072.C016879.packed 128 cuts16879 = true := by
 decide +kernel
def pointBounds16879 : List (Nat × Nat × Nat) := [(2216329216,97813979146048,97814358177943),(2216398848,97814394685113,97814773717263)]
theorem point_links_checked16879 : (cuts16879.take 2).map (fun c => (2216296449-1+2*2^9*c.k,97813781277827+c.lower,97814160309598+c.upper)) = pointBounds16879 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000214
