import PlattAssemblyKernel
import PlattCertificates.Count131072.C028864
import PlattCertificates.Count131072.C028865
import PlattCertificates.Count131072.C028866
import PlattCertificates.Count131072.C028867
import PlattCertificates.Count131072.C028868
import PlattCertificates.Count131072.C028869
import PlattCertificates.Count131072.C028870
import PlattCertificates.Count131072.C028871
import PlattCertificates.Count131072.C028872
import PlattCertificates.Count131072.C028873
import PlattCertificates.Count131072.C028874
import PlattCertificates.Count131072.C028875
import PlattCertificates.Count131072.C028876
import PlattCertificates.Count131072.C028877
import PlattCertificates.Count131072.C028878
import PlattCertificates.Count131072.C028879
import PlattCertificates.Count131072.C028880
import PlattCertificates.Count131072.C028881
import PlattCertificates.Count131072.C028882
import PlattCertificates.Count131072.C028883
import PlattCertificates.Count131072.C028884
import PlattCertificates.Count131072.C028885
import PlattCertificates.Count131072.C028886
import PlattCertificates.Count131072.C028887
import PlattCertificates.Count131072.C028888
import PlattCertificates.Count131072.C028889
import PlattCertificates.Count131072.C028890
import PlattCertificates.Count131072.C028891
import PlattCertificates.Count131072.C028892
import PlattCertificates.Count131072.C028893
import PlattCertificates.Count131072.C028894
import PlattCertificates.Count131072.C028895
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000277
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28864 : List PrefixCut := [⟨3,10999771,10999777⟩,
⟨119,408843211,408843444⟩,
⟨128,439909103,439909354⟩]
theorem checked28864 : checkPrefixCuts (2^48) 3787194369 9 Manual.Count131072.C028864.packed 128 cuts28864 = true := by
 decide +kernel
def pointBounds28864 : List (Nat × Nat × Nat) := [(3787197440,104736314925999,104736697971552),(3787316224,104736712769439,104737095815219)]
theorem point_links_checked28864 : (cuts28864.take 2).map (fun c => (3787194369-1+2*2^9*c.k,104736303926228+c.lower,104736686971775+c.upper)) = pointBounds28864 := by
 decide +kernel
def cuts28865 : List PrefixCut := [⟨107,370852601,370852812⟩,
⟨128,439745265,439745515⟩]
theorem checked28865 : checkPrefixCuts (2^48) 3787325441 9 Manual.Count131072.C028865.packed 128 cuts28865 = true := by
 decide +kernel
def pointBounds28865 : List (Nat × Nat × Nat) := [(3787435008,104737114687932,104737497733941)]
theorem point_links_checked28865 : (cuts28865.take 1).map (fun c => (3787325441-1+2*2^9*c.k,104736743835331+c.lower,104737126881129+c.upper)) = pointBounds28865 := by
 decide +kernel
def cuts28866 : List PrefixCut := [⟨95,329148655,329148841⟩,
⟨128,442553984,442554231⟩]
theorem checked28866 : checkPrefixCuts (2^48) 3787456513 9 Manual.Count131072.C028866.packed 128 cuts28866 = true := by
 decide +kernel
def pointBounds28866 : List (Nat × Nat × Nat) := [(3787553792,104737512729251,104737895775485)]
theorem point_links_checked28866 : (cuts28866.take 1).map (fun c => (3787456513-1+2*2^9*c.k,104737183580596+c.lower,104737566626644+c.upper)) = pointBounds28866 := by
 decide +kernel
def cuts28867 : List PrefixCut := [⟨83,286184171,286184335⟩,
⟨128,443207473,443207724⟩]
theorem checked28867 : checkPrefixCuts (2^48) 3787587585 9 Manual.Count131072.C028867.packed 128 cuts28867 = true := by
 decide +kernel
def pointBounds28867 : List (Nat × Nat × Nat) := [(3787672576,104737912318751,104738295365210)]
theorem point_links_checked28867 : (cuts28867.take 1).map (fun c => (3787587585-1+2*2^9*c.k,104737626134580+c.lower,104738009180875+c.upper)) = pointBounds28867 := by
 decide +kernel
def cuts28868 : List PrefixCut := [⟨71,244485817,244485951⟩,
⟨128,440442633,440442876⟩]
theorem checked28868 : checkPrefixCuts (2^48) 3787718657 9 Manual.Count131072.C028868.packed 128 cuts28868 = true := by
 decide +kernel
def pointBounds28868 : List (Nat × Nat × Nat) := [(3787791360,104738313827870,104738696874550)]
theorem point_links_checked28868 : (cuts28868.take 1).map (fun c => (3787718657-1+2*2^9*c.k,104738069342053+c.lower,104738452388599+c.upper)) = pointBounds28868 := by
 decide +kernel
def cuts28869 : List PrefixCut := [⟨59,204350715,204350828⟩,
⟨128,444217149,444217397⟩]
theorem checked28869 : checkPrefixCuts (2^48) 3787849729 9 Manual.Count131072.C028869.packed 128 cuts28869 = true := by
 decide +kernel
def pointBounds28869 : List (Nat × Nat × Nat) := [(3787910144,104738714135401,104739097182303)]
theorem point_links_checked28869 : (cuts28869.take 1).map (fun c => (3787849729-1+2*2^9*c.k,104738509784686+c.lower,104738892831475+c.upper)) = pointBounds28869 := by
 decide +kernel
def cuts28870 : List PrefixCut := [⟨47,159611229,159611319⟩,
⟨128,440486465,440486711⟩]
theorem checked28870 : checkPrefixCuts (2^48) 3787980801 9 Manual.Count131072.C028870.packed 128 cuts28870 = true := by
 decide +kernel
def pointBounds28870 : List (Nat × Nat × Nat) := [(3788028928,104739113613064,104739496660191)]
theorem point_links_checked28870 : (cuts28870.take 1).map (fun c => (3787980801-1+2*2^9*c.k,104738954001835+c.lower,104739337048872+c.upper)) = pointBounds28870 := by
 decide +kernel
def cuts28871 : List PrefixCut := [⟨35,119110036,119110103⟩,
⟨128,443369035,443369282⟩]
theorem checked28871 : checkPrefixCuts (2^48) 3788111873 9 Manual.Count131072.C028871.packed 128 cuts28871 = true := by
 decide +kernel
def pointBounds28871 : List (Nat × Nat × Nat) := [(3788147712,104739513598336,104739896645686)]
theorem point_links_checked28871 : (cuts28871.take 1).map (fun c => (3788111873-1+2*2^9*c.k,104739394488300+c.lower,104739777535583+c.upper)) = pointBounds28871 := by
 decide +kernel
def cuts28872 : List PrefixCut := [⟨23,78314310,78314352⟩,
⟨128,442610725,442610969⟩]
theorem checked28872 : checkPrefixCuts (2^48) 3788242945 9 Manual.Count131072.C028872.packed 128 cuts28872 = true := by
 decide +kernel
def pointBounds28872 : List (Nat × Nat × Nat) := [(3788266496,104739916171645,104740299219217)]
theorem point_links_checked28872 : (cuts28872.take 1).map (fun c => (3788242945-1+2*2^9*c.k,104739837857335+c.lower,104740220904865+c.upper)) = pointBounds28872 := by
 decide +kernel
def cuts28873 : List PrefixCut := [⟨11,38264267,38264289⟩,
⟨127,440515135,440515379⟩,
⟨128,443635613,443635859⟩]
theorem checked28873 : checkPrefixCuts (2^48) 3788374017 9 Manual.Count131072.C028873.packed 128 cuts28873 = true := by
 decide +kernel
def pointBounds28873 : List (Nat × Nat × Nat) := [(3788385280,104740318732327,104740701780123),(3788504064,104740720983195,104741104031213)]
theorem point_links_checked28873 : (cuts28873.take 2).map (fun c => (3788374017-1+2*2^9*c.k,104740280468060+c.lower,104740663515834+c.upper)) = pointBounds28873 := by
 decide +kernel
def cuts28874 : List PrefixCut := [⟨115,395774422,395774647⟩,
⟨128,439533969,439534218⟩]
theorem checked28874 : checkPrefixCuts (2^48) 3788505089 9 Manual.Count131072.C028874.packed 128 cuts28874 = true := by
 decide +kernel
def pointBounds28874 : List (Nat × Nat × Nat) := [(3788622848,104741119878095,104741502926340)]
theorem point_links_checked28874 : (cuts28874.take 1).map (fun c => (3788505089-1+2*2^9*c.k,104740724103673+c.lower,104741107151693+c.upper)) = pointBounds28874 := by
 decide +kernel
def cuts28875 : List PrefixCut := [⟨103,350665223,350665422⟩,
⟨128,438478600,438478847⟩]
theorem checked28875 : checkPrefixCuts (2^48) 3788636161 9 Manual.Count131072.C028875.packed 128 cuts28875 = true := by
 decide +kernel
def pointBounds28875 : List (Nat × Nat × Nat) := [(3788741632,104741514302865,104741897351333)]
theorem point_links_checked28875 : (cuts28875.take 1).map (fun c => (3788636161-1+2*2^9*c.k,104741163637642+c.lower,104741546685911+c.upper)) = pointBounds28875 := by
 decide +kernel
def cuts28876 : List PrefixCut := [⟨91,314548213,314548387⟩,
⟨128,442103709,442103955⟩]
theorem checked28876 : checkPrefixCuts (2^48) 3788767233 9 Manual.Count131072.C028876.packed 128 cuts28876 = true := by
 decide +kernel
def pointBounds28876 : List (Nat × Nat × Nat) := [(3788860416,104741916664455,104742299713145)]
theorem point_links_checked28876 : (cuts28876.take 1).map (fun c => (3788767233-1+2*2^9*c.k,104741602116242+c.lower,104741985164758+c.upper)) = pointBounds28876 := by
 decide +kernel
def cuts28877 : List PrefixCut := [⟨79,271079034,271079187⟩,
⟨128,443054136,443054381⟩]
theorem checked28877 : checkPrefixCuts (2^48) 3788898305 9 Manual.Count131072.C028877.packed 128 cuts28877 = true := by
 decide +kernel
def pointBounds28877 : List (Nat × Nat × Nat) := [(3788979200,104742315298985,104742698347900)]
theorem point_links_checked28877 : (cuts28877.take 1).map (fun c => (3788898305-1+2*2^9*c.k,104742044219951+c.lower,104742427268713+c.upper)) = pointBounds28877 := by
 decide +kernel
def cuts28878 : List PrefixCut := [⟨67,234744181,234744311⟩,
⟨128,447793126,447793376⟩]
theorem checked28878 : checkPrefixCuts (2^48) 3789029377 9 Manual.Count131072.C028878.packed 128 cuts28878 = true := by
 decide +kernel
def pointBounds28878 : List (Nat × Nat × Nat) := [(3789097984,104742722018268,104743105067405)]
theorem point_links_checked28878 : (cuts28878.take 1).map (fun c => (3789029377-1+2*2^9*c.k,104742487274087+c.lower,104742870323094+c.upper)) = pointBounds28878 := by
 decide +kernel
def cuts28879 : List PrefixCut := [⟨55,192617606,192617715⟩,
⟨128,441537929,441538178⟩]
theorem checked28879 : checkPrefixCuts (2^48) 3789160449 9 Manual.Count131072.C028879.packed 128 cuts28879 = true := by
 decide +kernel
def pointBounds28879 : List (Nat × Nat × Nat) := [(3789216768,104743127684819,104743510734185)]
theorem point_links_checked28879 : (cuts28879.take 1).map (fun c => (3789160449-1+2*2^9*c.k,104742935067213+c.lower,104743318116470+c.upper)) = pointBounds28879 := by
 decide +kernel
def cuts28880 : List PrefixCut := [⟨43,150345235,150345318⟩,
⟨128,444048180,444048425⟩]
theorem checked28880 : checkPrefixCuts (2^48) 3789291521 9 Manual.Count131072.C028880.packed 128 cuts28880 = true := by
 decide +kernel
def pointBounds28880 : List (Nat × Nat × Nat) := [(3789335552,104743526950377,104743909999966)]
theorem point_links_checked28880 : (cuts28880.take 1).map (fun c => (3789291521-1+2*2^9*c.k,104743376605142+c.lower,104743759654648+c.upper)) = pointBounds28880 := by
 decide +kernel
def cuts28881 : List PrefixCut := [⟨31,107704236,107704299⟩,
⟨128,439724644,439724896⟩]
theorem checked28881 : checkPrefixCuts (2^48) 3789422593 9 Manual.Count131072.C028881.packed 128 cuts28881 = true := by
 decide +kernel
def pointBounds28881 : List (Nat × Nat × Nat) := [(3789454336,104743928357558,104744311407372)]
theorem point_links_checked28881 : (cuts28881.take 1).map (fun c => (3789422593-1+2*2^9*c.k,104743820653322+c.lower,104744203703073+c.upper)) = pointBounds28881 := by
 decide +kernel
def cuts28882 : List PrefixCut := [⟨19,64249032,64249068⟩,
⟨128,439040971,439041216⟩]
theorem checked28882 : checkPrefixCuts (2^48) 3789553665 9 Manual.Count131072.C028882.packed 128 cuts28882 = true := by
 decide +kernel
def pointBounds28882 : List (Nat × Nat × Nat) := [(3789573120,104744324626998,104744707677037)]
theorem point_links_checked28882 : (cuts28882.take 1).map (fun c => (3789553665-1+2*2^9*c.k,104744260377966+c.lower,104744643427969+c.upper)) = pointBounds28882 := by
 decide +kernel
def cuts28883 : List PrefixCut := [⟨7,24807480,24807495⟩,
⟨123,420235129,420235370⟩,
⟨128,435980675,435980924⟩]
theorem checked28883 : checkPrefixCuts (2^48) 3789684737 9 Manual.Count131072.C028883.packed 128 cuts28883 = true := by
 decide +kernel
def pointBounds28883 : List (Nat × Nat × Nat) := [(3789691904,104744724226417,104745107276680),(3789810688,104745119654066,104745502704555)]
theorem point_links_checked28883 : (cuts28883.take 2).map (fun c => (3789684737-1+2*2^9*c.k,104744699418937+c.lower,104745082469185+c.upper)) = pointBounds28883 := by
 decide +kernel
def cuts28884 : List PrefixCut := [⟨111,382863229,382863445⟩,
⟨128,441907078,441907324⟩]
theorem checked28884 : checkPrefixCuts (2^48) 3789815809 9 Manual.Count131072.C028884.packed 128 cuts28884 = true := by
 decide +kernel
def pointBounds28884 : List (Nat × Nat × Nat) := [(3789929472,104745518262841,104745901313554)]
theorem point_links_checked28884 : (cuts28884.take 1).map (fun c => (3789815809-1+2*2^9*c.k,104745135399612+c.lower,104745518450109+c.upper)) = pointBounds28884 := by
 decide +kernel
def cuts28885 : List PrefixCut := [⟨99,344082813,344083003⟩,
⟨128,442708782,442709027⟩]
theorem checked28885 : checkPrefixCuts (2^48) 3789946881 9 Manual.Count131072.C028885.packed 128 cuts28885 = true := by
 decide +kernel
def pointBounds28885 : List (Nat × Nat × Nat) := [(3790048256,104745921389503,104746304440436)]
theorem point_links_checked28885 : (cuts28885.take 1).map (fun c => (3789946881-1+2*2^9*c.k,104745577306690+c.lower,104745960357433+c.upper)) = pointBounds28885 := by
 decide +kernel
def cuts28886 : List PrefixCut := [⟨87,297804178,297804345⟩,
⟨128,438831702,438831951⟩]
theorem checked28886 : checkPrefixCuts (2^48) 3790077953 9 Manual.Count131072.C028886.packed 128 cuts28886 = true := by
 decide +kernel
def pointBounds28886 : List (Nat × Nat × Nat) := [(3790167040,104746317819650,104746700870805)]
theorem point_links_checked28886 : (cuts28886.take 1).map (fun c => (3790077953-1+2*2^9*c.k,104746020015472+c.lower,104746403066460+c.upper)) = pointBounds28886 := by
 decide +kernel
def cuts28887 : List PrefixCut := [⟨75,259994548,259994694⟩,
⟨128,441861346,441861590⟩]
theorem checked28887 : checkPrefixCuts (2^48) 3790209025 9 Manual.Count131072.C028887.packed 128 cuts28887 = true := by
 decide +kernel
def pointBounds28887 : List (Nat × Nat × Nat) := [(3790285824,104746718841722,104747101893105)]
theorem point_links_checked28887 : (cuts28887.take 1).map (fun c => (3790209025-1+2*2^9*c.k,104746458847174+c.lower,104746841898411+c.upper)) = pointBounds28887 := by
 decide +kernel
def cuts28888 : List PrefixCut := [⟨63,218919932,218920056⟩,
⟨128,443182715,443182967⟩]
theorem checked28888 : checkPrefixCuts (2^48) 3790340097 9 Manual.Count131072.C028888.packed 128 cuts28888 = true := by
 decide +kernel
def pointBounds28888 : List (Nat × Nat × Nat) := [(3790404608,104747119628452,104747502680057)]
theorem point_links_checked28888 : (cuts28888.take 1).map (fun c => (3790340097-1+2*2^9*c.k,104746900708520+c.lower,104747283760001+c.upper)) = pointBounds28888 := by
 decide +kernel
def cuts28889 : List PrefixCut := [⟨51,172724217,172724315⟩,
⟨128,438192139,438192383⟩]
theorem checked28889 : checkPrefixCuts (2^48) 3790471169 9 Manual.Count131072.C028889.packed 128 cuts28889 = true := by
 decide +kernel
def pointBounds28889 : List (Nat × Nat × Nat) := [(3790523392,104747516615452,104747899667283)]
theorem point_links_checked28889 : (cuts28889.take 1).map (fun c => (3790471169-1+2*2^9*c.k,104747343891235+c.lower,104747726942968+c.upper)) = pointBounds28889 := by
 decide +kernel
def cuts28890 : List PrefixCut := [⟨39,133734311,133734385⟩,
⟨128,436543353,436543596⟩]
theorem checked28890 : checkPrefixCuts (2^48) 3790602241 9 Manual.Count131072.C028890.packed 128 cuts28890 = true := by
 decide +kernel
def pointBounds28890 : List (Nat × Nat × Nat) := [(3790642176,104747915817685,104748298869736)]
theorem point_links_checked28890 : (cuts28890.take 1).map (fun c => (3790602241-1+2*2^9*c.k,104747782083374+c.lower,104748165135351+c.upper)) = pointBounds28890 := by
 decide +kernel
def cuts28891 : List PrefixCut := [⟨27,94524246,94524299⟩,
⟨128,442319915,442320164⟩]
theorem checked28891 : checkPrefixCuts (2^48) 3790733313 9 Manual.Count131072.C028891.packed 128 cuts28891 = true := by
 decide +kernel
def pointBounds28891 : List (Nat × Nat × Nat) := [(3790760960,104748313150973,104748696203246)]
theorem point_links_checked28891 : (cuts28891.take 1).map (fun c => (3790733313-1+2*2^9*c.k,104748218626727+c.lower,104748601678947+c.upper)) = pointBounds28891 := by
 decide +kernel
def cuts28892 : List PrefixCut := [⟨15,50861729,50861759⟩,
⟨128,442007653,442007901⟩]
theorem checked28892 : checkPrefixCuts (2^48) 3790864385 9 Manual.Count131072.C028892.packed 128 cuts28892 = true := by
 decide +kernel
def pointBounds28892 : List (Nat × Nat × Nat) := [(3790879744,104748711808371,104749094860870)]
theorem point_links_checked28892 : (cuts28892.take 1).map (fun c => (3790864385-1+2*2^9*c.k,104748660946642+c.lower,104749043999111+c.upper)) = pointBounds28892 := by
 decide +kernel
def cuts28893 : List PrefixCut := [⟨3,10246259,10246265⟩,
⟨119,408136256,408136480⟩,
⟨128,439913461,439913702⟩]
theorem checked28893 : checkPrefixCuts (2^48) 3790995457 9 Manual.Count131072.C028893.packed 128 cuts28893 = true := by
 decide +kernel
def pointBounds28893 : List (Nat × Nat × Nat) := [(3790998528,104749113200554,104749496253277),(3791117312,104749511090551,104749894143492)]
theorem point_links_checked28893 : (cuts28893.take 2).map (fun c => (3790995457-1+2*2^9*c.k,104749102954295+c.lower,104749486007012+c.upper)) = pointBounds28893 := by
 decide +kernel
def cuts28894 : List PrefixCut := [⟨107,364986703,364986908⟩,
⟨128,439972497,439972743⟩]
theorem checked28894 : checkPrefixCuts (2^48) 3791126529 9 Manual.Count131072.C028894.packed 128 cuts28894 = true := by
 decide +kernel
def pointBounds28894 : List (Nat × Nat × Nat) := [(3791236096,104749907854459,104750290907622)]
theorem point_links_checked28894 : (cuts28894.take 1).map (fun c => (3791126529-1+2*2^9*c.k,104749542867756+c.lower,104749925920714+c.upper)) = pointBounds28894 := by
 decide +kernel
def cuts28895 : List PrefixCut := [⟨95,328447477,328447661⟩,
⟨128,440848219,440848462⟩]
theorem checked28895 : checkPrefixCuts (2^48) 3791257601 9 Manual.Count131072.C028895.packed 128 cuts28895 = true := by
 decide +kernel
def pointBounds28895 : List (Nat × Nat × Nat) := [(3791354880,104750311287730,104750694341118)]
theorem point_links_checked28895 : (cuts28895.take 1).map (fun c => (3791257601-1+2*2^9*c.k,104749982840253+c.lower,104750365893457+c.upper)) = pointBounds28895 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000277
