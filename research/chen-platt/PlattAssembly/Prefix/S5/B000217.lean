import PlattAssemblyKernel
import PlattCertificates.Count131072.C046944
import PlattCertificates.Count131072.C046945
import PlattCertificates.Count131072.C046946
import PlattCertificates.Count131072.C046947
import PlattCertificates.Count131072.C046948
import PlattCertificates.Count131072.C046949
import PlattCertificates.Count131072.C046950
import PlattCertificates.Count131072.C046951
import PlattCertificates.Count131072.C046952
import PlattCertificates.Count131072.C046953
import PlattCertificates.Count131072.C046954
import PlattCertificates.Count131072.C046955
import PlattCertificates.Count131072.C046956
import PlattCertificates.Count131072.C046957
import PlattCertificates.Count131072.C046958
import PlattCertificates.Count131072.C046959
import PlattCertificates.Count131072.C046960
import PlattCertificates.Count131072.C046961
import PlattCertificates.Count131072.C046962
import PlattCertificates.Count131072.C046963
import PlattCertificates.Count131072.C046964
import PlattCertificates.Count131072.C046965
import PlattCertificates.Count131072.C046966
import PlattCertificates.Count131072.C046967
import PlattCertificates.Count131072.C046968
import PlattCertificates.Count131072.C046969
import PlattCertificates.Count131072.C046970
import PlattCertificates.Count131072.C046971
import PlattCertificates.Count131072.C046972
import PlattCertificates.Count131072.C046973
import PlattCertificates.Count131072.C046974
import PlattCertificates.Count131072.C046975
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000217
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46944 : List PrefixCut := [⟨64,265792424,265792582⟩]
theorem checked46944 : checkPrefixCuts (2^48) 6156976129 10 Manual.Count131072.C046944.packed 64 cuts46944 = true := by
 decide +kernel
def cuts46945 : List PrefixCut := [⟨4,16091826,16091835⟩,
⟨64,267981108,267981260⟩]
theorem checked46945 : checkPrefixCuts (2^48) 6157107201 10 Manual.Count131072.C046945.packed 64 cuts46945 = true := by
 decide +kernel
def pointBounds46945 : List (Nat × Nat × Nat) := [(6157115392,110871195717462,110871582390593)]
theorem point_links_checked46945 : (cuts46945.take 1).map (fun c => (6157107201-1+2*2^10*c.k,110871179625636+c.lower,110871566298758+c.upper)) = pointBounds46945 := by
 decide +kernel
def cuts46946 : List PrefixCut := [⟨34,137371210,137371294⟩,
⟨64,262078265,262078418⟩]
theorem checked46946 : checkPrefixCuts (2^48) 6157238273 10 Manual.Count131072.C046946.packed 64 cuts46946 = true := by
 decide +kernel
def pointBounds46946 : List (Nat × Nat × Nat) := [(6157307904,110871584977954,110871971651312)]
theorem point_links_checked46946 : (cuts46946.take 1).map (fun c => (6157238273-1+2*2^10*c.k,110871447606744+c.lower,110871834280018+c.upper)) = pointBounds46946 := by
 decide +kernel
def cuts46947 : List PrefixCut := [⟨64,266598292,266598446⟩]
theorem checked46947 : checkPrefixCuts (2^48) 6157369345 10 Manual.Count131072.C046947.packed 64 cuts46947 = true := by
 decide +kernel
def pointBounds46947 : List (Nat × Nat × Nat) := [(6157500416,110871976283301,110872362956882)]
theorem point_links_checked46947 : (cuts46947.take 1).map (fun c => (6157369345-1+2*2^10*c.k,110871709685009+c.lower,110872096358436+c.upper)) = pointBounds46947 := by
 decide +kernel
def cuts46948 : List PrefixCut := [⟨64,266821204,266821358⟩]
theorem checked46948 : checkPrefixCuts (2^48) 6157500417 10 Manual.Count131072.C046948.packed 64 cuts46948 = true := by
 decide +kernel
def cuts46949 : List PrefixCut := [⟨30,121866386,121866462⟩,
⟨64,261238731,261238885⟩]
theorem checked46949 : checkPrefixCuts (2^48) 6157631489 10 Manual.Count131072.C046949.packed 64 cuts46949 = true := by
 decide +kernel
def pointBounds46949 : List (Nat × Nat × Nat) := [(6157692928,110872364970891,110872751644702)]
theorem point_links_checked46949 : (cuts46949.take 1).map (fun c => (6157631489-1+2*2^10*c.k,110872243104505+c.lower,110872629778240+c.upper)) = pointBounds46949 := by
 decide +kernel
def cuts46950 : List PrefixCut := [⟨60,250262935,250263079⟩,
⟨64,267632597,267632751⟩]
theorem checked46950 : checkPrefixCuts (2^48) 6157762561 10 Manual.Count131072.C046950.packed 64 cuts46950 = true := by
 decide +kernel
def pointBounds46950 : List (Nat × Nat × Nat) := [(6157885440,110872754606171,110873141280204)]
theorem point_links_checked46950 : (cuts46950.take 1).map (fun c => (6157762561-1+2*2^10*c.k,110872504343236+c.lower,110872891017125+c.upper)) = pointBounds46950 := by
 decide +kernel
def cuts46951 : List PrefixCut := [⟨64,266804140,266804286⟩]
theorem checked46951 : checkPrefixCuts (2^48) 6157893633 10 Manual.Count131072.C046951.packed 64 cuts46951 = true := by
 decide +kernel
def cuts46952 : List PrefixCut := [⟨26,107826204,107826263⟩,
⟨64,266432795,266432952⟩]
theorem checked46952 : checkPrefixCuts (2^48) 6158024705 10 Manual.Count131072.C046952.packed 64 cuts46952 = true := by
 decide +kernel
def pointBounds46952 : List (Nat × Nat × Nat) := [(6158077952,110873146606177,110873533280425)]
theorem point_links_checked46952 : (cuts46952.take 1).map (fun c => (6158024705-1+2*2^10*c.k,110873038779973+c.lower,110873425454162+c.upper)) = pointBounds46952 := by
 decide +kernel
def cuts46953 : List PrefixCut := [⟨56,232695535,232695676⟩,
⟨64,264781674,264781833⟩]
theorem checked46953 : checkPrefixCuts (2^48) 6158155777 10 Manual.Count131072.C046953.packed 64 cuts46953 = true := by
 decide +kernel
def pointBounds46953 : List (Nat × Nat × Nat) := [(6158270464,110873537908303,110873924582790)]
theorem point_links_checked46953 : (cuts46953.take 1).map (fun c => (6158155777-1+2*2^10*c.k,110873305212768+c.lower,110873691887114+c.upper)) = pointBounds46953 := by
 decide +kernel
def cuts46954 : List PrefixCut := [⟨64,265141677,265141826⟩]
theorem checked46954 : checkPrefixCuts (2^48) 6158286849 10 Manual.Count131072.C046954.packed 64 cuts46954 = true := by
 decide +kernel
def cuts46955 : List PrefixCut := [⟨22,89308639,89308692⟩,
⟨64,267969727,267969878⟩]
theorem checked46955 : checkPrefixCuts (2^48) 6158417921 10 Manual.Count131072.C046955.packed 64 cuts46955 = true := by
 decide +kernel
def pointBounds46955 : List (Nat × Nat × Nat) := [(6158462976,110873924444758,110874311119465)]
theorem point_links_checked46955 : (cuts46955.take 1).map (fun c => (6158417921-1+2*2^10*c.k,110873835136119+c.lower,110874221810773+c.upper)) = pointBounds46955 := by
 decide +kernel
def cuts46956 : List PrefixCut := [⟨52,213987751,213987873⟩,
⟨64,264719038,264719189⟩]
theorem checked46956 : checkPrefixCuts (2^48) 6158548993 10 Manual.Count131072.C046956.packed 64 cuts46956 = true := by
 decide +kernel
def pointBounds46956 : List (Nat × Nat × Nat) := [(6158655488,110874317093597,110874703768524)]
theorem point_links_checked46956 : (cuts46956.take 1).map (fun c => (6158548993-1+2*2^10*c.k,110874103105846+c.lower,110874489780651+c.upper)) = pointBounds46956 := by
 decide +kernel
def cuts46957 : List PrefixCut := [⟨64,267364215,267364372⟩]
theorem checked46957 : checkPrefixCuts (2^48) 6158680065 10 Manual.Count131072.C046957.packed 64 cuts46957 = true := by
 decide +kernel
def cuts46958 : List PrefixCut := [⟨18,73946906,73946946⟩,
⟨64,266718678,266718824⟩]
theorem checked46958 : checkPrefixCuts (2^48) 6158811137 10 Manual.Count131072.C046958.packed 64 cuts46958 = true := by
 decide +kernel
def pointBounds46958 : List (Nat × Nat × Nat) := [(6158848000,110874709136005,110875095811158)]
theorem point_links_checked46958 : (cuts46958.take 1).map (fun c => (6158811137-1+2*2^10*c.k,110874635189099+c.lower,110875021864212+c.upper)) = pointBounds46958 := by
 decide +kernel
def cuts46959 : List PrefixCut := [⟨48,198115807,198115924⟩,
⟨64,263376799,263376953⟩]
theorem checked46959 : checkPrefixCuts (2^48) 6158942209 10 Manual.Count131072.C046959.packed 64 cuts46959 = true := by
 decide +kernel
def pointBounds46959 : List (Nat × Nat × Nat) := [(6159040512,110875100023584,110875486698960)]
theorem point_links_checked46959 : (cuts46959.take 1).map (fun c => (6158942209-1+2*2^10*c.k,110874901907777+c.lower,110875288583036+c.upper)) = pointBounds46959 := by
 decide +kernel
def cuts46960 : List PrefixCut := [⟨64,266478826,266478979⟩]
theorem checked46960 : checkPrefixCuts (2^48) 6159073281 10 Manual.Count131072.C046960.packed 64 cuts46960 = true := by
 decide +kernel
def cuts46961 : List PrefixCut := [⟨14,60963497,60963530⟩,
⟨64,269123744,269123897⟩]
theorem checked46961 : checkPrefixCuts (2^48) 6159204353 10 Manual.Count131072.C046961.packed 64 cuts46961 = true := by
 decide +kernel
def pointBounds46961 : List (Nat × Nat × Nat) := [(6159233024,110875492726899,110875879402498)]
theorem point_links_checked46961 : (cuts46961.take 1).map (fun c => (6159204353-1+2*2^10*c.k,110875431763402+c.lower,110875818438968+c.upper)) = pointBounds46961 := by
 decide +kernel
def cuts46962 : List PrefixCut := [⟨44,182565799,182565906⟩,
⟨64,266787373,266787526⟩]
theorem checked46962 : checkPrefixCuts (2^48) 6159335425 10 Manual.Count131072.C046962.packed 64 cuts46962 = true := by
 decide +kernel
def pointBounds46962 : List (Nat × Nat × Nat) := [(6159425536,110875883452945,110876270128771)]
theorem point_links_checked46962 : (cuts46962.take 1).map (fun c => (6159335425-1+2*2^10*c.k,110875700887146+c.lower,110876087562865+c.upper)) = pointBounds46962 := by
 decide +kernel
def cuts46963 : List PrefixCut := [⟨64,265273663,265273816⟩]
theorem checked46963 : checkPrefixCuts (2^48) 6159466497 10 Manual.Count131072.C046963.packed 64 cuts46963 = true := by
 decide +kernel
def cuts46964 : List PrefixCut := [⟨10,40807319,40807343⟩,
⟨64,262389170,262389325⟩]
theorem checked46964 : checkPrefixCuts (2^48) 6159597569 10 Manual.Count131072.C046964.packed 64 cuts46964 = true := by
 decide +kernel
def pointBounds46964 : List (Nat × Nat × Nat) := [(6159618048,110876273755501,110876660431550)]
theorem point_links_checked46964 : (cuts46964.take 1).map (fun c => (6159597569-1+2*2^10*c.k,110876232948182+c.lower,110876619624207+c.upper)) = pointBounds46964 := by
 decide +kernel
def cuts46965 : List PrefixCut := [⟨40,167977338,167977437⟩,
⟨64,268689559,268689712⟩]
theorem checked46965 : checkPrefixCuts (2^48) 6159728641 10 Manual.Count131072.C046965.packed 64 cuts46965 = true := by
 decide +kernel
def pointBounds46965 : List (Nat × Nat × Nat) := [(6159810560,110876663314690,110877049990969)]
theorem point_links_checked46965 : (cuts46965.take 1).map (fun c => (6159728641-1+2*2^10*c.k,110876495337352+c.lower,110876882013532+c.upper)) = pointBounds46965 := by
 decide +kernel
def cuts46966 : List PrefixCut := [⟨64,262606465,262606609⟩]
theorem checked46966 : checkPrefixCuts (2^48) 6159859713 10 Manual.Count131072.C046966.packed 64 cuts46966 = true := by
 decide +kernel
def cuts46967 : List PrefixCut := [⟨6,25223089,25223104⟩,
⟨64,266027921,266028075⟩]
theorem checked46967 : checkPrefixCuts (2^48) 6159990785 10 Manual.Count131072.C046967.packed 64 cuts46967 = true := by
 decide +kernel
def pointBounds46967 : List (Nat × Nat × Nat) := [(6160003072,110877051856465,110877438532957)]
theorem point_links_checked46967 : (cuts46967.take 1).map (fun c => (6159990785-1+2*2^10*c.k,110877026633376+c.lower,110877413309853+c.upper)) = pointBounds46967 := by
 decide +kernel
def cuts46968 : List PrefixCut := [⟨36,152842417,152842502⟩,
⟨64,270225972,270226131⟩]
theorem checked46968 : checkPrefixCuts (2^48) 6160121857 10 Manual.Count131072.C046968.packed 64 cuts46968 = true := by
 decide +kernel
def pointBounds46968 : List (Nat × Nat × Nat) := [(6160195584,110877445503714,110877832180430)]
theorem point_links_checked46968 : (cuts46968.take 1).map (fun c => (6160121857-1+2*2^10*c.k,110877292661297+c.lower,110877679337928+c.upper)) = pointBounds46968 := by
 decide +kernel
def cuts46969 : List PrefixCut := [⟨64,260670656,260670814⟩]
theorem checked46969 : checkPrefixCuts (2^48) 6160252929 10 Manual.Count131072.C046969.packed 64 cuts46969 = true := by
 decide +kernel
def cuts46970 : List PrefixCut := [⟨2,8407165,8407170⟩,
⟨64,265462621,265462770⟩]
theorem checked46970 : checkPrefixCuts (2^48) 6160384001 10 Manual.Count131072.C046970.packed 64 cuts46970 = true := by
 decide +kernel
def pointBounds46970 : List (Nat × Nat × Nat) := [(6160388096,110877831965090,110878218642043)]
theorem point_links_checked46970 : (cuts46970.take 1).map (fun c => (6160384001-1+2*2^10*c.k,110877823557925+c.lower,110878210234873+c.upper)) = pointBounds46970 := by
 decide +kernel
def cuts46971 : List PrefixCut := [⟨32,134054199,134054274⟩,
⟨64,267969913,267970064⟩]
theorem checked46971 : checkPrefixCuts (2^48) 6160515073 10 Manual.Count131072.C046971.packed 64 cuts46971 = true := by
 decide +kernel
def pointBounds46971 : List (Nat × Nat × Nat) := [(6160580608,110878223074745,110878609751917)]
theorem point_links_checked46971 : (cuts46971.take 1).map (fun c => (6160515073-1+2*2^10*c.k,110878089020546+c.lower,110878475697643+c.upper)) = pointBounds46971 := by
 decide +kernel
def cuts46972 : List PrefixCut := [⟨63,259740302,259740450⟩,
⟨64,263395360,263395510⟩]
theorem checked46972 : checkPrefixCuts (2^48) 6160646145 10 Manual.Count131072.C046972.packed 64 cuts46972 = true := by
 decide +kernel
def pointBounds46972 : List (Nat × Nat × Nat) := [(6160775168,110878616730761,110879003408157)]
theorem point_links_checked46972 : (cuts46972.take 1).map (fun c => (6160646145-1+2*2^10*c.k,110878356990459+c.lower,110878743667707+c.upper)) = pointBounds46972 := by
 decide +kernel
def cuts46973 : List PrefixCut := [⟨64,266222375,266222527⟩]
theorem checked46973 : checkPrefixCuts (2^48) 6160777217 10 Manual.Count131072.C046973.packed 64 cuts46973 = true := by
 decide +kernel
def cuts46974 : List PrefixCut := [⟨30,124816920,124816993⟩,
⟨64,265577099,265577256⟩]
theorem checked46974 : checkPrefixCuts (2^48) 6160908289 10 Manual.Count131072.C046974.packed 64 cuts46974 = true := by
 decide +kernel
def pointBounds46974 : List (Nat × Nat × Nat) := [(6160969728,110879011425114,110879398102737)]
theorem point_links_checked46974 : (cuts46974.take 1).map (fun c => (6160908289-1+2*2^10*c.k,110878886608194+c.lower,110879273285744+c.upper)) = pointBounds46974 := by
 decide +kernel
def cuts46975 : List PrefixCut := [⟨61,254881113,254881258⟩,
⟨64,267901428,267901582⟩]
theorem checked46975 : checkPrefixCuts (2^48) 6161039361 10 Manual.Count131072.C046975.packed 64 cuts46975 = true := by
 decide +kernel
def pointBounds46975 : List (Nat × Nat × Nat) := [(6161164288,110879407066406,110879793744258)]
theorem point_links_checked46975 : (cuts46975.take 1).map (fun c => (6161039361-1+2*2^10*c.k,110879152185293+c.lower,110879538863000+c.upper)) = pointBounds46975 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000217
