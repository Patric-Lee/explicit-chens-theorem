import PlattAssemblyKernel
import PlattCertificates.Count131072.C026880
import PlattCertificates.Count131072.C026881
import PlattCertificates.Count131072.C026882
import PlattCertificates.Count131072.C026883
import PlattCertificates.Count131072.C026884
import PlattCertificates.Count131072.C026885
import PlattCertificates.Count131072.C026886
import PlattCertificates.Count131072.C026887
import PlattCertificates.Count131072.C026888
import PlattCertificates.Count131072.C026889
import PlattCertificates.Count131072.C026890
import PlattCertificates.Count131072.C026891
import PlattCertificates.Count131072.C026892
import PlattCertificates.Count131072.C026893
import PlattCertificates.Count131072.C026894
import PlattCertificates.Count131072.C026895
import PlattCertificates.Count131072.C026896
import PlattCertificates.Count131072.C026897
import PlattCertificates.Count131072.C026898
import PlattCertificates.Count131072.C026899
import PlattCertificates.Count131072.C026900
import PlattCertificates.Count131072.C026901
import PlattCertificates.Count131072.C026902
import PlattCertificates.Count131072.C026903
import PlattCertificates.Count131072.C026904
import PlattCertificates.Count131072.C026905
import PlattCertificates.Count131072.C026906
import PlattCertificates.Count131072.C026907
import PlattCertificates.Count131072.C026908
import PlattCertificates.Count131072.C026909
import PlattCertificates.Count131072.C026910
import PlattCertificates.Count131072.C026911
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000215
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26880 : List PrefixCut := [⟨32,118506042,118506107⟩,
⟨128,472820499,472820763⟩]
theorem checked26880 : checkPrefixCuts (2^48) 3527147521 9 Manual.Count131072.C026880.packed 128 cuts26880 = true := by
 decide +kernel
def pointBounds26880 : List (Nat × Nat × Nat) := [(3527180288,103827020198521,103827402735141)]
theorem point_links_checked26880 : (cuts26880.take 1).map (fun c => (3527147521-1+2*2^9*c.k,103826901692479+c.lower,103827284229034+c.upper)) = pointBounds26880 := by
 decide +kernel
def cuts26881 : List PrefixCut := [⟨12,45405810,45405835⟩,
⟨120,448544930,448545189⟩,
⟨128,475356579,475356855⟩]
theorem checked26881 : checkPrefixCuts (2^48) 3527278593 9 Manual.Count131072.C026881.packed 128 cuts26881 = true := by
 decide +kernel
def pointBounds26881 : List (Nat × Nat × Nat) := [(3527290880,103827419918788,103827802455632),(3527401472,103827823057908,103828205594986)]
theorem point_links_checked26881 : (cuts26881.take 2).map (fun c => (3527278593-1+2*2^9*c.k,103827374512978+c.lower,103827757049797+c.upper)) = pointBounds26881 := by
 decide +kernel
def cuts26882 : List PrefixCut := [⟨100,375596650,375596861⟩,
⟨128,482360817,482361089⟩]
theorem checked26882 : checkPrefixCuts (2^48) 3527409665 9 Manual.Count131072.C026882.packed 128 cuts26882 = true := by
 decide +kernel
def pointBounds26882 : List (Nat × Nat × Nat) := [(3527512064,103828225466207,103828608003513)]
theorem point_links_checked26882 : (cuts26882.take 1).map (fun c => (3527409665-1+2*2^9*c.k,103827849869557+c.lower,103828232406652+c.upper)) = pointBounds26882 := by
 decide +kernel
def cuts26883 : List PrefixCut := [⟨80,298903026,298903197⟩,
⟨128,476996771,476997042⟩]
theorem checked26883 : checkPrefixCuts (2^48) 3527540737 9 Manual.Count131072.C026883.packed 128 cuts26883 = true := by
 decide +kernel
def pointBounds26883 : List (Nat × Nat × Nat) := [(3527622656,103828631133400,103829013670938)]
theorem point_links_checked26883 : (cuts26883.take 1).map (fun c => (3527540737-1+2*2^9*c.k,103828332230374+c.lower,103828714767741+c.upper)) = pointBounds26883 := by
 decide +kernel
def cuts26884 : List PrefixCut := [⟨60,220379632,220379755⟩,
⟨128,469399186,469399451⟩]
theorem checked26884 : checkPrefixCuts (2^48) 3527671809 9 Manual.Count131072.C026884.packed 128 cuts26884 = true := by
 decide +kernel
def pointBounds26884 : List (Nat × Nat × Nat) := [(3527733248,103829029606777,103829412144538)]
theorem point_links_checked26884 : (cuts26884.take 1).map (fun c => (3527671809-1+2*2^9*c.k,103828809227145+c.lower,103829191764783+c.upper)) = pointBounds26884 := by
 decide +kernel
def cuts26885 : List PrefixCut := [⟨40,149201947,149202028⟩,
⟨128,477440111,477440377⟩]
theorem checked26885 : checkPrefixCuts (2^48) 3527802881 9 Manual.Count131072.C026885.packed 128 cuts26885 = true := by
 decide +kernel
def pointBounds26885 : List (Nat × Nat × Nat) := [(3527843840,103829427828278,103829810366262)]
theorem point_links_checked26885 : (cuts26885.take 1).map (fun c => (3527802881-1+2*2^9*c.k,103829278626331+c.lower,103829661164234+c.upper)) = pointBounds26885 := by
 decide +kernel
def cuts26886 : List PrefixCut := [⟨20,75555827,75555867⟩,
⟨128,475427839,475428104⟩]
theorem checked26886 : checkPrefixCuts (2^48) 3527933953 9 Manual.Count131072.C026886.packed 128 cuts26886 = true := by
 decide +kernel
def pointBounds26886 : List (Nat × Nat × Nat) := [(3527954432,103829831622269,103830214160478),(3528065024,103830231494281,103830614032715)]
theorem point_links_checked26886 : (cuts26886.take 2).map (fun c => (3527933953-1+2*2^9*c.k,103829756066442+c.lower,103830138604611+c.upper)) = pointBounds26886 := by
 decide +kernel
def cuts26887 : List PrefixCut := [⟨108,404167546,404167772⟩,
⟨128,476606813,476607080⟩]
theorem checked26887 : checkPrefixCuts (2^48) 3528065025 9 Manual.Count131072.C026887.packed 128 cuts26887 = true := by
 decide +kernel
def pointBounds26887 : List (Nat × Nat × Nat) := [(3528175616,103830635661827,103831018200487)]
theorem point_links_checked26887 : (cuts26887.take 1).map (fun c => (3528065025-1+2*2^9*c.k,103830231494281+c.lower,103830614032715+c.upper)) = pointBounds26887 := by
 decide +kernel
def cuts26888 : List PrefixCut := [⟨88,328524480,328524662⟩,
⟨128,479540811,479541079⟩]
theorem checked26888 : checkPrefixCuts (2^48) 3528196097 9 Manual.Count131072.C026888.packed 128 cuts26888 = true := by
 decide +kernel
def pointBounds26888 : List (Nat × Nat × Nat) := [(3528286208,103831036625574,103831419164457)]
theorem point_links_checked26888 : (cuts26888.take 1).map (fun c => (3528196097-1+2*2^9*c.k,103830708101094+c.lower,103831090639795+c.upper)) = pointBounds26888 := by
 decide +kernel
def cuts26889 : List PrefixCut := [⟨68,251450652,251450789⟩,
⟨128,470907450,470907707⟩]
theorem checked26889 : checkPrefixCuts (2^48) 3528327169 9 Manual.Count131072.C026889.packed 128 cuts26889 = true := by
 decide +kernel
def pointBounds26889 : List (Nat × Nat × Nat) := [(3528396800,103831439092557,103831821631663)]
theorem point_links_checked26889 : (cuts26889.take 1).map (fun c => (3528327169-1+2*2^9*c.k,103831187641905+c.lower,103831570180874+c.upper)) = pointBounds26889 := by
 decide +kernel
def cuts26890 : List PrefixCut := [⟨48,180205426,180205528⟩,
⟨128,470570882,470571152⟩]
theorem checked26890 : checkPrefixCuts (2^48) 3528458241 9 Manual.Count131072.C026890.packed 128 cuts26890 = true := by
 decide +kernel
def pointBounds26890 : List (Nat × Nat × Nat) := [(3528507392,103831838754781,103832221294109)]
theorem point_links_checked26890 : (cuts26890.take 1).map (fun c => (3528458241-1+2*2^9*c.k,103831658549355+c.lower,103832041088581+c.upper)) = pointBounds26890 := by
 decide +kernel
def cuts26891 : List PrefixCut := [⟨28,105455255,105455314⟩,
⟨128,481003012,481003276⟩]
theorem checked26891 : checkPrefixCuts (2^48) 3528589313 9 Manual.Count131072.C026891.packed 128 cuts26891 = true := by
 decide +kernel
def pointBounds26891 : List (Nat × Nat × Nat) := [(3528617984,103832234575492,103832617115047)]
theorem point_links_checked26891 : (cuts26891.take 1).map (fun c => (3528589313-1+2*2^9*c.k,103832129120237+c.lower,103832511659733+c.upper)) = pointBounds26891 := by
 decide +kernel
def cuts26892 : List PrefixCut := [⟨8,28875565,28875581⟩,
⟨116,429058657,429058898⟩,
⟨128,473726511,473726778⟩]
theorem checked26892 : checkPrefixCuts (2^48) 3528720385 9 Manual.Count131072.C026892.packed 128 cuts26892 = true := by
 decide +kernel
def pointBounds26892 : List (Nat × Nat × Nat) := [(3528728576,103832638998814,103833021538590),(3528839168,103833039181906,103833421721907)]
theorem point_links_checked26892 : (cuts26892.take 2).map (fun c => (3528720385-1+2*2^9*c.k,103832610123249+c.lower,103832992663009+c.upper)) = pointBounds26892 := by
 decide +kernel
def cuts26893 : List PrefixCut := [⟨96,357018200,357018400⟩,
⟨128,477537509,477537776⟩]
theorem checked26893 : checkPrefixCuts (2^48) 3528851457 9 Manual.Count131072.C026893.packed 128 cuts26893 = true := by
 decide +kernel
def pointBounds26893 : List (Nat × Nat × Nat) := [(3528949760,103833440867960,103833823408187)]
theorem point_links_checked26893 : (cuts26893.take 1).map (fun c => (3528851457-1+2*2^9*c.k,103833083849760+c.lower,103833466389787+c.upper)) = pointBounds26893 := by
 decide +kernel
def cuts26894 : List PrefixCut := [⟨76,277405430,277405585⟩,
⟨128,476642323,476642588⟩]
theorem checked26894 : checkPrefixCuts (2^48) 3528982529 9 Manual.Count131072.C026894.packed 128 cuts26894 = true := by
 decide +kernel
def pointBounds26894 : List (Nat × Nat × Nat) := [(3529060352,103833838792699,103834221333148)]
theorem point_links_checked26894 : (cuts26894.take 1).map (fun c => (3528982529-1+2*2^9*c.k,103833561387269+c.lower,103833943927563+c.upper)) = pointBounds26894 := by
 decide +kernel
def cuts26895 : List PrefixCut := [⟨56,202344306,202344422⟩,
⟨128,473274892,473275155⟩]
theorem checked26895 : checkPrefixCuts (2^48) 3529113601 9 Manual.Count131072.C026895.packed 128 cuts26895 = true := by
 decide +kernel
def pointBounds26895 : List (Nat × Nat × Nat) := [(3529170944,103834240373898,103834622914573)]
theorem point_links_checked26895 : (cuts26895.take 1).map (fun c => (3529113601-1+2*2^9*c.k,103834038029592+c.lower,103834420570151+c.upper)) = pointBounds26895 := by
 decide +kernel
def cuts26896 : List PrefixCut := [⟨36,133110393,133110467⟩,
⟨128,466478328,466478592⟩]
theorem checked26896 : checkPrefixCuts (2^48) 3529244673 9 Manual.Count131072.C026896.packed 128 cuts26896 = true := by
 decide +kernel
def pointBounds26896 : List (Nat × Nat × Nat) := [(3529281536,103834644414877,103835026955773)]
theorem point_links_checked26896 : (cuts26896.take 1).map (fun c => (3529244673-1+2*2^9*c.k,103834511304484+c.lower,103834893845306+c.upper)) = pointBounds26896 := by
 decide +kernel
def cuts26897 : List PrefixCut := [⟨16,58139099,58139133⟩,
⟨124,451547935,451548191⟩,
⟨128,467338261,467338525⟩]
theorem checked26897 : checkPrefixCuts (2^48) 3529375745 9 Manual.Count131072.C026897.packed 128 cuts26897 = true := by
 decide +kernel
def pointBounds26897 : List (Nat × Nat × Nat) := [(3529392128,103835035921911,103835418463031),(3529502720,103835429330747,103835811872089)]
theorem point_links_checked26897 : (cuts26897.take 2).map (fun c => (3529375745-1+2*2^9*c.k,103834977782812+c.lower,103835360323898+c.upper)) = pointBounds26897 := by
 decide +kernel
def cuts26898 : List PrefixCut := [⟨104,388053152,388053363⟩,
⟨128,473780520,473780780⟩]
theorem checked26898 : checkPrefixCuts (2^48) 3529506817 9 Manual.Count131072.C026898.packed 128 cuts26898 = true := by
 decide +kernel
def pointBounds26898 : List (Nat × Nat × Nat) := [(3529613312,103835833174225,103836215715786)]
theorem point_links_checked26898 : (cuts26898.take 1).map (fun c => (3529506817-1+2*2^9*c.k,103835445121073+c.lower,103835827662423+c.upper)) = pointBounds26898 := by
 decide +kernel
def cuts26899 : List PrefixCut := [⟨84,315710982,315711157⟩,
⟨128,477431130,477431397⟩]
theorem checked26899 : checkPrefixCuts (2^48) 3529637889 9 Manual.Count131072.C026899.packed 128 cuts26899 = true := by
 decide +kernel
def pointBounds26899 : List (Nat × Nat × Nat) := [(3529723904,103836234612575,103836617154360)]
theorem point_links_checked26899 : (cuts26899.take 1).map (fun c => (3529637889-1+2*2^9*c.k,103835918901593+c.lower,103836301443203+c.upper)) = pointBounds26899 := by
 decide +kernel
def cuts26900 : List PrefixCut := [⟨64,235080633,235080763⟩,
⟨128,477572809,477573070⟩]
theorem checked26900 : checkPrefixCuts (2^48) 3529768961 9 Manual.Count131072.C026900.packed 128 cuts26900 = true := by
 decide +kernel
def pointBounds26900 : List (Nat × Nat × Nat) := [(3529834496,103836631413356,103837013955363)]
theorem point_links_checked26900 : (cuts26900.take 1).map (fun c => (3529768961-1+2*2^9*c.k,103836396332723+c.lower,103836778874600+c.upper)) = pointBounds26900 := by
 decide +kernel
def cuts26901 : List PrefixCut := [⟨44,168250717,168250810⟩,
⟨128,481701514,481701783⟩]
theorem checked26901 : checkPrefixCuts (2^48) 3529900033 9 Manual.Count131072.C026901.packed 128 cuts26901 = true := by
 decide +kernel
def pointBounds26901 : List (Nat × Nat × Nat) := [(3529945088,103837042156249,103837424698480)]
theorem point_links_checked26901 : (cuts26901.take 1).map (fun c => (3529900033-1+2*2^9*c.k,103836873905532+c.lower,103837256447670+c.upper)) = pointBounds26901 := by
 decide +kernel
def cuts26902 : List PrefixCut := [⟨24,89624322,89624375⟩,
⟨128,473231657,473231928⟩]
theorem checked26902 : checkPrefixCuts (2^48) 3530031105 9 Manual.Count131072.C026902.packed 128 cuts26902 = true := by
 decide +kernel
def pointBounds26902 : List (Nat × Nat × Nat) := [(3530055680,103837445231368,103837827773828)]
theorem point_links_checked26902 : (cuts26902.take 1).map (fun c => (3530031105-1+2*2^9*c.k,103837355607046+c.lower,103837738149453+c.upper)) = pointBounds26902 := by
 decide +kernel
def cuts26903 : List PrefixCut := [⟨4,15867109,15867119⟩,
⟨112,412857386,412857623⟩,
⟨128,472416809,472417081⟩]
theorem checked26903 : checkPrefixCuts (2^48) 3530162177 9 Manual.Count131072.C026903.packed 128 cuts26903 = true := by
 decide +kernel
def pointBounds26903 : List (Nat × Nat × Nat) := [(3530166272,103837844705812,103838227248500),(3530276864,103838241696089,103838624239004)]
theorem point_links_checked26903 : (cuts26903.take 2).map (fun c => (3530162177-1+2*2^9*c.k,103837828838703+c.lower,103838211381381+c.upper)) = pointBounds26903 := by
 decide +kernel
def cuts26904 : List PrefixCut := [⟨92,340846764,340846955⟩,
⟨128,476784301,476784570⟩]
theorem checked26904 : checkPrefixCuts (2^48) 3530293249 9 Manual.Count131072.C026904.packed 128 cuts26904 = true := by
 decide +kernel
def pointBounds26904 : List (Nat × Nat × Nat) := [(3530387456,103838642102276,103839024645417)]
theorem point_links_checked26904 : (cuts26904.take 1).map (fun c => (3530293249-1+2*2^9*c.k,103838301255512+c.lower,103838683798462+c.upper)) = pointBounds26904 := by
 decide +kernel
def cuts26905 : List PrefixCut := [⟨72,269478983,269479132⟩,
⟨128,473099281,473099551⟩]
theorem checked26905 : checkPrefixCuts (2^48) 3530424321 9 Manual.Count131072.C026905.packed 128 cuts26905 = true := by
 decide +kernel
def pointBounds26905 : List (Nat × Nat × Nat) := [(3530498048,103839047518796,103839430062164)]
theorem point_links_checked26905 : (cuts26905.take 1).map (fun c => (3530424321-1+2*2^9*c.k,103838778039813+c.lower,103839160583032+c.upper)) = pointBounds26905 := by
 decide +kernel
def cuts26906 : List PrefixCut := [⟨52,191180036,191180145⟩,
⟨128,473480277,473480541⟩]
theorem checked26906 : checkPrefixCuts (2^48) 3530555393 9 Manual.Count131072.C026906.packed 128 cuts26906 = true := by
 decide +kernel
def pointBounds26906 : List (Nat × Nat × Nat) := [(3530608640,103839442319130,103839824862728)]
theorem point_links_checked26906 : (cuts26906.take 1).map (fun c => (3530555393-1+2*2^9*c.k,103839251139094+c.lower,103839633682583+c.upper)) = pointBounds26906 := by
 decide +kernel
def cuts26907 : List PrefixCut := [⟨32,115118656,115118724⟩,
⟨128,467802456,467802724⟩]
theorem checked26907 : checkPrefixCuts (2^48) 3530686465 9 Manual.Count131072.C026907.packed 128 cuts26907 = true := by
 decide +kernel
def pointBounds26907 : List (Nat × Nat × Nat) := [(3530719232,103839839738027,103840222281848)]
theorem point_links_checked26907 : (cuts26907.take 1).map (fun c => (3530686465-1+2*2^9*c.k,103839724619371+c.lower,103840107163124+c.upper)) = pointBounds26907 := by
 decide +kernel
def cuts26908 : List PrefixCut := [⟨12,44403667,44403690⟩,
⟨120,445305170,445305419⟩,
⟨128,473763997,473764263⟩]
theorem checked26908 : checkPrefixCuts (2^48) 3530817537 9 Manual.Count131072.C026908.packed 128 cuts26908 = true := by
 decide +kernel
def pointBounds26908 : List (Nat × Nat × Nat) := [(3530829824,103840236825494,103840619369538),(3530940416,103840637726997,103841020271267)]
theorem point_links_checked26908 : (cuts26908.take 2).map (fun c => (3530817537-1+2*2^9*c.k,103840192421827+c.lower,103840574965848+c.upper)) = pointBounds26908 := by
 decide +kernel
def cuts26909 : List PrefixCut := [⟨100,368524106,368524315⟩,
⟨128,472869568,472869836⟩]
theorem checked26909 : checkPrefixCuts (2^48) 3530948609 9 Manual.Count131072.C026909.packed 128 cuts26909 = true := by
 decide +kernel
def pointBounds26909 : List (Nat × Nat × Nat) := [(3531051008,103841034709930,103841417254426)]
theorem point_links_checked26909 : (cuts26909.take 1).map (fun c => (3530948609-1+2*2^9*c.k,103840666185824+c.lower,103841048730111+c.upper)) = pointBounds26909 := by
 decide +kernel
def cuts26910 : List PrefixCut := [⟨80,298683221,298683389⟩,
⟨128,475482554,475482819⟩]
theorem checked26910 : checkPrefixCuts (2^48) 3531079681 9 Manual.Count131072.C026910.packed 128 cuts26910 = true := by
 decide +kernel
def pointBounds26910 : List (Nat × Nat × Nat) := [(3531161600,103841437738613,103841820283336)]
theorem point_links_checked26910 : (cuts26910.take 1).map (fun c => (3531079681-1+2*2^9*c.k,103841139055392+c.lower,103841521599947+c.upper)) = pointBounds26910 := by
 decide +kernel
def cuts26911 : List PrefixCut := [⟨60,227412354,227412483⟩,
⟨128,481283663,481283933⟩]
theorem checked26911 : checkPrefixCuts (2^48) 3531210753 9 Manual.Count131072.C026911.packed 128 cuts26911 = true := by
 decide +kernel
def pointBounds26911 : List (Nat × Nat × Nat) := [(3531272192,103841841950300,103842224495249)]
theorem point_links_checked26911 : (cuts26911.take 1).map (fun c => (3531210753-1+2*2^9*c.k,103841614537946+c.lower,103841997082766+c.upper)) = pointBounds26911 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000215
