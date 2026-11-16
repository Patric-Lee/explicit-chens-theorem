import PlattAssemblyKernel
import PlattCertificates.Count131072.C059024
import PlattCertificates.Count131072.C059025
import PlattCertificates.Count131072.C059026
import PlattCertificates.Count131072.C059027
import PlattCertificates.Count131072.C059028
import PlattCertificates.Count131072.C059029
import PlattCertificates.Count131072.C059030
import PlattCertificates.Count131072.C059031
import PlattCertificates.Count131072.C059032
import PlattCertificates.Count131072.C059033
import PlattCertificates.Count131072.C059034
import PlattCertificates.Count131072.C059035
import PlattCertificates.Count131072.C059036
import PlattCertificates.Count131072.C059037
import PlattCertificates.Count131072.C059038
import PlattCertificates.Count131072.C059039
import PlattCertificates.Count131072.C059040
import PlattCertificates.Count131072.C059041
import PlattCertificates.Count131072.C059042
import PlattCertificates.Count131072.C059043
import PlattCertificates.Count131072.C059044
import PlattCertificates.Count131072.C059045
import PlattCertificates.Count131072.C059046
import PlattCertificates.Count131072.C059047
import PlattCertificates.Count131072.C059048
import PlattCertificates.Count131072.C059049
import PlattCertificates.Count131072.C059050
import PlattCertificates.Count131072.C059051
import PlattCertificates.Count131072.C059052
import PlattCertificates.Count131072.C059053
import PlattCertificates.Count131072.C059054
import PlattCertificates.Count131072.C059055
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000282
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59024 : List PrefixCut := [⟨64,209422735,209422852⟩]
theorem checked59024 : checkPrefixCuts (2^48) 7740325889 10 Manual.Count131072.C059024.packed 64 cuts59024 = true := by
 decide +kernel
def cuts59025 : List PrefixCut := [⟨39,131746527,131746599⟩,
⟨64,214655589,214655706⟩]
theorem checked59025 : checkPrefixCuts (2^48) 7740456961 10 Manual.Count131072.C059025.packed 64 cuts59025 = true := by
 decide +kernel
def pointBounds59025 : List (Nat × Nat × Nat) := [(7740536832,113714546214329,113714934506125)]
theorem point_links_checked59025 : (cuts59025.take 1).map (fun c => (7740456961-1+2*2^10*c.k,113714414467802+c.lower,113714802759526+c.upper)) = pointBounds59025 := by
 decide +kernel
def cuts59026 : List PrefixCut := [⟨64,204215710,204215820⟩]
theorem checked59026 : checkPrefixCuts (2^48) 7740588033 10 Manual.Count131072.C059026.packed 64 cuts59026 = true := by
 decide +kernel
def cuts59027 : List PrefixCut := [⟨30,97561237,97561294⟩,
⟨64,211593830,211593950⟩]
theorem checked59027 : checkPrefixCuts (2^48) 7740719105 10 Manual.Count131072.C059027.packed 64 cuts59027 = true := by
 decide +kernel
def pointBounds59027 : List (Nat × Nat × Nat) := [(7740780544,113714930900338,113715319192346)]
theorem point_links_checked59027 : (cuts59027.take 1).map (fun c => (7740719105-1+2*2^10*c.k,113714833339101+c.lower,113715221631052+c.upper)) = pointBounds59027 := by
 decide +kernel
def cuts59028 : List PrefixCut := [⟨64,206281408,206281529⟩]
theorem checked59028 : checkPrefixCuts (2^48) 7740850177 10 Manual.Count131072.C059028.packed 64 cuts59028 = true := by
 decide +kernel
def cuts59029 : List PrefixCut := [⟨21,69486930,69486971⟩,
⟨64,208968666,208968786⟩]
theorem checked59029 : checkPrefixCuts (2^48) 7740981249 10 Manual.Count131072.C059029.packed 64 cuts59029 = true := by
 decide +kernel
def pointBounds59029 : List (Nat × Nat × Nat) := [(7741024256,113715320701269,113715708993502)]
theorem point_links_checked59029 : (cuts59029.take 1).map (fun c => (7740981249-1+2*2^10*c.k,113715251214339+c.lower,113715639506531+c.upper)) = pointBounds59029 := by
 decide +kernel
def cuts59030 : List PrefixCut := [⟨64,210237751,210237867⟩]
theorem checked59030 : checkPrefixCuts (2^48) 7741112321 10 Manual.Count131072.C059030.packed 64 cuts59030 = true := by
 decide +kernel
def cuts59031 : List PrefixCut := [⟨12,40032760,40032784⟩,
⟨64,211979489,211979612⟩]
theorem checked59031 : checkPrefixCuts (2^48) 7741243393 10 Manual.Count131072.C059031.packed 64 cuts59031 = true := by
 decide +kernel
def pointBounds59031 : List (Nat × Nat × Nat) := [(7741267968,113715710453516,113716098745968)]
theorem point_links_checked59031 : (cuts59031.take 1).map (fun c => (7741243393-1+2*2^10*c.k,113715670420756+c.lower,113716058713184+c.upper)) = pointBounds59031 := by
 decide +kernel
def cuts59032 : List PrefixCut := [⟨64,206740122,206740237⟩]
theorem checked59032 : checkPrefixCuts (2^48) 7741374465 10 Manual.Count131072.C059032.packed 64 cuts59032 = true := by
 decide +kernel
def cuts59033 : List PrefixCut := [⟨3,9926056,9926062⟩,
⟨64,207827388,207827504⟩]
theorem checked59033 : checkPrefixCuts (2^48) 7741505537 10 Manual.Count131072.C059033.packed 64 cuts59033 = true := by
 decide +kernel
def pointBounds59033 : List (Nat × Nat × Nat) := [(7741511680,113716099066423,113716487359095)]
theorem point_links_checked59033 : (cuts59033.take 1).map (fun c => (7741505537-1+2*2^10*c.k,113716089140367+c.lower,113716477433033+c.upper)) = pointBounds59033 := by
 decide +kernel
def cuts59034 : List PrefixCut := [⟨58,189026800,189026910⟩,
⟨64,209496350,209496472⟩]
theorem checked59034 : checkPrefixCuts (2^48) 7741636609 10 Manual.Count131072.C059034.packed 64 cuts59034 = true := by
 decide +kernel
def pointBounds59034 : List (Nat × Nat × Nat) := [(7741755392,113716485994555,113716874287447)]
theorem point_links_checked59034 : (cuts59034.take 1).map (fun c => (7741636609-1+2*2^10*c.k,113716296967755+c.lower,113716685260537+c.upper)) = pointBounds59034 := by
 decide +kernel
def cuts59035 : List PrefixCut := [⟨64,213310353,213310475⟩]
theorem checked59035 : checkPrefixCuts (2^48) 7741767681 10 Manual.Count131072.C059035.packed 64 cuts59035 = true := by
 decide +kernel
def cuts59036 : List PrefixCut := [⟨49,160153065,160153160⟩,
⟨64,210143671,210143794⟩]
theorem checked59036 : checkPrefixCuts (2^48) 7741898753 10 Manual.Count131072.C059036.packed 64 cuts59036 = true := by
 decide +kernel
def pointBounds59036 : List (Nat × Nat × Nat) := [(7741999104,113716879927523,113717268220644)]
theorem point_links_checked59036 : (cuts59036.take 1).map (fun c => (7741898753-1+2*2^10*c.k,113716719774458+c.lower,113717108067484+c.upper)) = pointBounds59036 := by
 decide +kernel
def cuts59037 : List PrefixCut := [⟨64,207158894,207159016⟩]
theorem checked59037 : checkPrefixCuts (2^48) 7742029825 10 Manual.Count131072.C059037.packed 64 cuts59037 = true := by
 decide +kernel
def cuts59038 : List PrefixCut := [⟨40,132190140,132190216⟩,
⟨64,210318352,210318474⟩]
theorem checked59038 : checkPrefixCuts (2^48) 7742160897 10 Manual.Count131072.C059038.packed 64 cuts59038 = true := by
 decide +kernel
def pointBounds59038 : List (Nat × Nat × Nat) := [(7742242816,113717269267163,113717657560510)]
theorem point_links_checked59038 : (cuts59038.take 1).map (fun c => (7742160897-1+2*2^10*c.k,113717137077023+c.lower,113717525370294+c.upper)) = pointBounds59038 := by
 decide +kernel
def cuts59039 : List PrefixCut := [⟨64,209005985,209006106⟩]
theorem checked59039 : checkPrefixCuts (2^48) 7742291969 10 Manual.Count131072.C059039.packed 64 cuts59039 = true := by
 decide +kernel
def cuts59040 : List PrefixCut := [⟨31,101975032,101975089⟩,
⟨64,209111536,209111656⟩]
theorem checked59040 : checkPrefixCuts (2^48) 7742423041 10 Manual.Count131072.C059040.packed 64 cuts59040 = true := by
 decide +kernel
def pointBounds59040 : List (Nat × Nat × Nat) := [(7742486528,113717658376392,113718046669963)]
theorem point_links_checked59040 : (cuts59040.take 1).map (fun c => (7742423041-1+2*2^10*c.k,113717556401360+c.lower,113717944694874+c.upper)) = pointBounds59040 := by
 decide +kernel
def cuts59041 : List PrefixCut := [⟨64,209507890,209508015⟩]
theorem checked59041 : checkPrefixCuts (2^48) 7742554113 10 Manual.Count131072.C059041.packed 64 cuts59041 = true := by
 decide +kernel
def cuts59042 : List PrefixCut := [⟨22,72925221,72925263⟩,
⟨64,210849417,210849535⟩]
theorem checked59042 : checkPrefixCuts (2^48) 7742685185 10 Manual.Count131072.C059042.packed 64 cuts59042 = true := by
 decide +kernel
def pointBounds59042 : List (Nat × Nat × Nat) := [(7742730240,113718047946007,113718436239808)]
theorem point_links_checked59042 : (cuts59042.take 1).map (fun c => (7742685185-1+2*2^10*c.k,113717975020786+c.lower,113718363314545+c.upper)) = pointBounds59042 := by
 decide +kernel
def cuts59043 : List PrefixCut := [⟨64,208955488,208955607⟩]
theorem checked59043 : checkPrefixCuts (2^48) 7742816257 10 Manual.Count131072.C059043.packed 64 cuts59043 = true := by
 decide +kernel
def cuts59044 : List PrefixCut := [⟨13,41005462,41005486⟩,
⟨64,211823744,211823864⟩]
theorem checked59044 : checkPrefixCuts (2^48) 7742947329 10 Manual.Count131072.C059044.packed 64 cuts59044 = true := by
 decide +kernel
def pointBounds59044 : List (Nat × Nat × Nat) := [(7742973952,113718435831153,113718824125173)]
theorem point_links_checked59044 : (cuts59044.take 1).map (fun c => (7742947329-1+2*2^10*c.k,113718394825691+c.lower,113718783119687+c.upper)) = pointBounds59044 := by
 decide +kernel
def cuts59045 : List PrefixCut := [⟨64,208003292,208003411⟩]
theorem checked59045 : checkPrefixCuts (2^48) 7743078401 10 Manual.Count131072.C059045.packed 64 cuts59045 = true := by
 decide +kernel
def cuts59046 : List PrefixCut := [⟨4,13558988,13558996⟩,
⟨64,210217151,210217275⟩]
theorem checked59046 : checkPrefixCuts (2^48) 7743209473 10 Manual.Count131072.C059046.packed 64 cuts59046 = true := by
 decide +kernel
def pointBounds59046 : List (Nat × Nat × Nat) := [(7743217664,113718828211715,113719216505958)]
theorem point_links_checked59046 : (cuts59046.take 1).map (fun c => (7743209473-1+2*2^10*c.k,113718814652727+c.lower,113719202946962+c.upper)) = pointBounds59046 := by
 decide +kernel
def cuts59047 : List PrefixCut := [⟨59,193819760,193819873⟩,
⟨64,211304103,211304226⟩]
theorem checked59047 : checkPrefixCuts (2^48) 7743340545 10 Manual.Count131072.C059047.packed 64 cuts59047 = true := by
 decide +kernel
def pointBounds59047 : List (Nat × Nat × Nat) := [(7743461376,113719218689638,113719606984110)]
theorem point_links_checked59047 : (cuts59047.take 1).map (fun c => (7743340545-1+2*2^10*c.k,113719024869878+c.lower,113719413164237+c.upper)) = pointBounds59047 := by
 decide +kernel
def cuts59048 : List PrefixCut := [⟨64,206829529,206829644⟩]
theorem checked59048 : checkPrefixCuts (2^48) 7743471617 10 Manual.Count131072.C059048.packed 64 cuts59048 = true := by
 decide +kernel
def cuts59049 : List PrefixCut := [⟨50,163752738,163752832⟩,
⟨64,209188739,209188857⟩]
theorem checked59049 : checkPrefixCuts (2^48) 7743602689 10 Manual.Count131072.C059049.packed 64 cuts59049 = true := by
 decide +kernel
def pointBounds59049 : List (Nat × Nat × Nat) := [(7743705088,113719606756248,113719995050939)]
theorem point_links_checked59049 : (cuts59049.take 1).map (fun c => (7743602689-1+2*2^10*c.k,113719443003510+c.lower,113719831298107+c.upper)) = pointBounds59049 := by
 decide +kernel
def cuts59050 : List PrefixCut := [⟨64,210311973,210312090⟩]
theorem checked59050 : checkPrefixCuts (2^48) 7743733761 10 Manual.Count131072.C059050.packed 64 cuts59050 = true := by
 decide +kernel
def cuts59051 : List PrefixCut := [⟨41,131833906,131833981⟩,
⟨64,207146158,207146276⟩]
theorem checked59051 : checkPrefixCuts (2^48) 7743864833 10 Manual.Count131072.C059051.packed 64 cuts59051 = true := by
 decide +kernel
def pointBounds59051 : List (Nat × Nat × Nat) := [(7743948800,113719994338128,113720382633035)]
theorem point_links_checked59051 : (cuts59051.take 1).map (fun c => (7743864833-1+2*2^10*c.k,113719862504222+c.lower,113720250799054+c.upper)) = pointBounds59051 := by
 decide +kernel
def cuts59052 : List PrefixCut := [⟨64,208160370,208160491⟩]
theorem checked59052 : checkPrefixCuts (2^48) 7743995905 10 Manual.Count131072.C059052.packed 64 cuts59052 = true := by
 decide +kernel
def cuts59053 : List PrefixCut := [⟨32,103515484,103515546⟩,
⟨64,209428961,209429084⟩]
theorem checked59053 : checkPrefixCuts (2^48) 7744126977 10 Manual.Count131072.C059053.packed 64 cuts59053 = true := by
 decide +kernel
def pointBounds59053 : List (Nat × Nat × Nat) := [(7744192512,113720381326234,113720769621367)]
theorem point_links_checked59053 : (cuts59053.take 1).map (fun c => (7744126977-1+2*2^10*c.k,113720277810750+c.lower,113720666105821+c.upper)) = pointBounds59053 := by
 decide +kernel
def cuts59054 : List PrefixCut := [⟨64,208044301,208044415⟩]
theorem checked59054 : checkPrefixCuts (2^48) 7744258049 10 Manual.Count131072.C059054.packed 64 cuts59054 = true := by
 decide +kernel
def cuts59055 : List PrefixCut := [⟨23,76034875,76034920⟩,
⟨64,209530926,209531048⟩]
theorem checked59055 : checkPrefixCuts (2^48) 7744389121 10 Manual.Count131072.C059055.packed 64 cuts59055 = true := by
 decide +kernel
def pointBounds59055 : List (Nat × Nat × Nat) := [(7744436224,113720771318887,113721159614240)]
theorem point_links_checked59055 : (cuts59055.take 1).map (fun c => (7744389121-1+2*2^10*c.k,113720695284012+c.lower,113721083579320+c.upper)) = pointBounds59055 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000282
