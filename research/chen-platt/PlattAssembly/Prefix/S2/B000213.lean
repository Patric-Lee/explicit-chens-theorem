import PlattAssemblyKernel
import PlattCertificates.Count131072.C016816
import PlattCertificates.Count131072.C016817
import PlattCertificates.Count131072.C016818
import PlattCertificates.Count131072.C016819
import PlattCertificates.Count131072.C016820
import PlattCertificates.Count131072.C016821
import PlattCertificates.Count131072.C016822
import PlattCertificates.Count131072.C016823
import PlattCertificates.Count131072.C016824
import PlattCertificates.Count131072.C016825
import PlattCertificates.Count131072.C016826
import PlattCertificates.Count131072.C016827
import PlattCertificates.Count131072.C016828
import PlattCertificates.Count131072.C016829
import PlattCertificates.Count131072.C016830
import PlattCertificates.Count131072.C016831
import PlattCertificates.Count131072.C016832
import PlattCertificates.Count131072.C016833
import PlattCertificates.Count131072.C016834
import PlattCertificates.Count131072.C016835
import PlattCertificates.Count131072.C016836
import PlattCertificates.Count131072.C016837
import PlattCertificates.Count131072.C016838
import PlattCertificates.Count131072.C016839
import PlattCertificates.Count131072.C016840
import PlattCertificates.Count131072.C016841
import PlattCertificates.Count131072.C016842
import PlattCertificates.Count131072.C016843
import PlattCertificates.Count131072.C016844
import PlattCertificates.Count131072.C016845
import PlattCertificates.Count131072.C016846
import PlattCertificates.Count131072.C016847
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000213
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16816 : List PrefixCut := [⟨4,26515260,26515276⟩,
⟨72,440936704,440936978⟩,
⟨128,786001780,786002269⟩]
theorem checked16816 : checkPrefixCuts (2^48) 2208038913 9 Manual.Count131072.C016816.packed 128 cuts16816 = true := by
 decide +kernel
def pointBounds16816 : List (Nat × Nat × Nat) := [(2208043008,97765008831811,97765387832971),(2208112640,97765423253255,97765802254673)]
theorem point_links_checked16816 : (cuts16816.take 2).map (fun c => (2208038913-1+2*2^9*c.k,97764982316551+c.lower,97765361317695+c.upper)) = pointBounds16816 := by
 decide +kernel
def cuts16817 : List PrefixCut := [⟨12,74314659,74314704⟩,
⟨80,489602273,489602579⟩,
⟨128,777797521,777798008⟩]
theorem checked16817 : checkPrefixCuts (2^48) 2208169985 9 Manual.Count131072.C016817.packed 128 cuts16817 = true := by
 decide +kernel
def pointBounds16817 : List (Nat × Nat × Nat) := [(2208182272,97765842632990,97766221634668),(2208251904,97766257920604,97766636922543)]
theorem point_links_checked16817 : (cuts16817.take 2).map (fun c => (2208169985-1+2*2^9*c.k,97765768318331+c.lower,97766147319964+c.upper)) = pointBounds16817 := by
 decide +kernel
def cuts16818 : List PrefixCut := [⟨20,122108212,122108288⟩,
⟨88,534183164,534183500⟩,
⟨128,778261035,778261528⟩]
theorem checked16818 : checkPrefixCuts (2^48) 2208301057 9 Manual.Count131072.C016818.packed 128 cuts16818 = true := by
 decide +kernel
def pointBounds16818 : List (Nat × Nat × Nat) := [(2208321536,97766668224064,97767047226260),(2208391168,97767080299016,97767459301472)]
theorem point_links_checked16818 : (cuts16818.take 2).map (fun c => (2208301057-1+2*2^9*c.k,97766546115852+c.lower,97766925117972+c.upper)) = pointBounds16818 := by
 decide +kernel
def cuts16819 : List PrefixCut := [⟨28,166199737,166199839⟩,
⟨96,586278202,586278568⟩,
⟨128,779616829,779617316⟩]
theorem checked16819 : checkPrefixCuts (2^48) 2208432129 9 Manual.Count131072.C016819.packed 128 cuts16819 = true := by
 decide +kernel
def pointBounds16819 : List (Nat × Nat × Nat) := [(2208460800,97767490576624,97767869579339),(2208530432,97767910655089,97768289658068)]
theorem point_links_checked16819 : (cuts16819.take 2).map (fun c => (2208432129-1+2*2^9*c.k,97767324376887+c.lower,97767703379500+c.upper)) = pointBounds16819 := by
 decide +kernel
def cuts16820 : List PrefixCut := [⟨36,214873923,214874063⟩,
⟨104,629828148,629828554⟩,
⟨128,776129495,776129992⟩]
theorem checked16820 : checkPrefixCuts (2^48) 2208563201 9 Manual.Count131072.C016820.packed 128 cuts16820 = true := by
 decide +kernel
def pointBounds16820 : List (Nat × Nat × Nat) := [(2208600064,97768318867639,97768697870879),(2208669696,97768733821864,97769112825370)]
theorem point_links_checked16820 : (cuts16820.take 2).map (fun c => (2208563201-1+2*2^9*c.k,97768103993716+c.lower,97768482996816+c.upper)) = pointBounds16820 := by
 decide +kernel
def cuts16821 : List PrefixCut := [⟨44,263924544,263924708⟩,
⟨112,671079043,671079456⟩,
⟨128,769456868,769457341⟩]
theorem checked16821 : checkPrefixCuts (2^48) 2208694273 9 Manual.Count131072.C016821.packed 128 cuts16821 = true := by
 decide +kernel
def pointBounds16821 : List (Nat × Nat × Nat) := [(2208739328,97769144047755,97769523051516),(2208808960,97769551202254,97769930206264)]
theorem point_links_checked16821 : (cuts16821.take 2).map (fun c => (2208694273-1+2*2^9*c.k,97768880123211+c.lower,97769259126808+c.upper)) = pointBounds16821 := by
 decide +kernel
def cuts16822 : List PrefixCut := [⟨52,321379484,321379686⟩,
⟨120,735007078,735007541⟩,
⟨128,782281611,782282103⟩]
theorem checked16822 : checkPrefixCuts (2^48) 2208825345 9 Manual.Count131072.C016822.packed 128 cuts16822 = true := by
 decide +kernel
def pointBounds16822 : List (Nat × Nat × Nat) := [(2208878592,97769970959563,97770349963835),(2208948224,97770384587157,97770763591690)]
theorem point_links_checked16822 : (cuts16822.take 2).map (fun c => (2208825345-1+2*2^9*c.k,97769649580079+c.lower,97770028584149+c.upper)) = pointBounds16822 := by
 decide +kernel
def cuts16823 : List PrefixCut := [⟨60,360096277,360096506⟩,
⟨128,768601013,768601497⟩]
theorem checked16823 : checkPrefixCuts (2^48) 2208956417 9 Manual.Count131072.C016823.packed 128 cuts16823 = true := by
 decide +kernel
def pointBounds16823 : List (Nat × Nat × Nat) := [(2209017856,97770791957967,97771170962758),(2209087488,97771200462703,97771579467749)]
theorem point_links_checked16823 : (cuts16823.take 2).map (fun c => (2208956417-1+2*2^9*c.k,97770431861690+c.lower,97770810866252+c.upper)) = pointBounds16823 := by
 decide +kernel
def cuts16824 : List PrefixCut := [⟨68,414225559,414225820⟩,
⟨128,782061206,782061702⟩]
theorem checked16824 : checkPrefixCuts (2^48) 2209087489 9 Manual.Count131072.C016824.packed 128 cuts16824 = true := by
 decide +kernel
def pointBounds16824 : List (Nat × Nat × Nat) := [(2209157120,97771614688262,97771993693569)]
theorem point_links_checked16824 : (cuts16824.take 1).map (fun c => (2209087489-1+2*2^9*c.k,97771200462703+c.lower,97771579467749+c.upper)) = pointBounds16824 := by
 decide +kernel
def cuts16825 : List PrefixCut := [⟨8,48925061,48925092⟩,
⟨76,461977759,461978042⟩,
⟨128,780358455,780358940⟩]
theorem checked16825 : checkPrefixCuts (2^48) 2209218561 9 Manual.Count131072.C016825.packed 128 cuts16825 = true := by
 decide +kernel
def pointBounds16825 : List (Nat × Nat × Nat) := [(2209226752,97772031448970,97772410454543),(2209296384,97772444501668,97772823507493)]
theorem point_links_checked16825 : (cuts16825.take 2).map (fun c => (2209218561-1+2*2^9*c.k,97771982523909+c.lower,97772361529451+c.upper)) = pointBounds16825 := by
 decide +kernel
def cuts16826 : List PrefixCut := [⟨16,94659111,94659172⟩,
⟨84,511125593,511125914⟩,
⟨128,783497039,783497528⟩]
theorem checked16826 : checkPrefixCuts (2^48) 2209349633 9 Manual.Count131072.C016826.packed 128 cuts16826 = true := by
 decide +kernel
def pointBounds16826 : List (Nat × Nat × Nat) := [(2209366016,97772857541475,97773236547563),(2209435648,97773274007957,97773653014305)]
theorem point_links_checked16826 : (cuts16826.take 2).map (fun c => (2209349633-1+2*2^9*c.k,97772762882364+c.lower,97773141888391+c.upper)) = pointBounds16826 := by
 decide +kernel
def cuts16827 : List PrefixCut := [⟨24,145355899,145355989⟩,
⟨92,556063537,556063884⟩,
⟨128,768291335,768291817⟩]
theorem checked16827 : checkPrefixCuts (2^48) 2209480705 9 Manual.Count131072.C016827.packed 128 cuts16827 = true := by
 decide +kernel
def pointBounds16827 : List (Nat × Nat × Nat) := [(2209505280,97773691735302,97774070741908),(2209574912,97774102442940,97774481449803)]
theorem point_links_checked16827 : (cuts16827.take 2).map (fun c => (2209480705-1+2*2^9*c.k,97773546379403+c.lower,97773925385919+c.upper)) = pointBounds16827 := by
 decide +kernel
def cuts16828 : List PrefixCut := [⟨32,191715392,191715512⟩,
⟨100,594499391,594499767⟩,
⟨128,763532460,763532944⟩]
theorem checked16828 : checkPrefixCuts (2^48) 2209611777 9 Manual.Count131072.C016828.packed 128 cuts16828 = true := by
 decide +kernel
def pointBounds16828 : List (Nat × Nat × Nat) := [(2209644544,97774506386130,97774885393248),(2209714176,97774909170129,97775288177503)]
theorem point_links_checked16828 : (cuts16828.take 2).map (fun c => (2209611777-1+2*2^9*c.k,97774314670738+c.lower,97774693677736+c.upper)) = pointBounds16828 := by
 decide +kernel
def cuts16829 : List PrefixCut := [⟨40,245584453,245584607⟩,
⟨108,653692825,653693240⟩,
⟨128,775460518,775461005⟩]
theorem checked16829 : checkPrefixCuts (2^48) 2209742849 9 Manual.Count131072.C016829.packed 128 cuts16829 = true := by
 decide +kernel
def pointBounds16829 : List (Nat × Nat × Nat) := [(2209783808,97775323787651,97775702795287),(2209853440,97775731896023,97776110903920)]
theorem point_links_checked16829 : (cuts16829.take 2).map (fun c => (2209742849-1+2*2^9*c.k,97775078203198+c.lower,97775457210680+c.upper)) = pointBounds16829 := by
 decide +kernel
def cuts16830 : List PrefixCut := [⟨48,288238469,288238650⟩,
⟨116,701033726,701034165⟩,
⟨128,768791513,768791994⟩]
theorem checked16830 : checkPrefixCuts (2^48) 2209873921 9 Manual.Count131072.C016830.packed 128 cuts16830 = true := by
 decide +kernel
def pointBounds16830 : List (Nat × Nat × Nat) := [(2209923072,97776141902185,97776520910335),(2209992704,97776554697442,97776933705850)]
theorem point_links_checked16830 : (cuts16830.take 2).map (fun c => (2209873921-1+2*2^9*c.k,97775853663716+c.lower,97776232671685+c.upper)) = pointBounds16830 := by
 decide +kernel
def cuts16831 : List PrefixCut := [⟨56,342986567,342986786⟩,
⟨124,755883128,755883605⟩,
⟨128,782627989,782628482⟩]
theorem checked16831 : checkPrefixCuts (2^48) 2210004993 9 Manual.Count131072.C016831.packed 128 cuts16831 = true := by
 decide +kernel
def pointBounds16831 : List (Nat × Nat × Nat) := [(2210062336,97776965441796,97777344450465),(2210131968,97777378338357,97777757347284)]
theorem point_links_checked16831 : (cuts16831.take 2).map (fun c => (2210004993-1+2*2^9*c.k,97776622455229+c.lower,97777001463679+c.upper)) = pointBounds16831 := by
 decide +kernel
def cuts16832 : List PrefixCut := [⟨64,386393459,386393706⟩,
⟨128,779652462,779652955⟩]
theorem checked16832 : checkPrefixCuts (2^48) 2210136065 9 Manual.Count131072.C016832.packed 128 cuts16832 = true := by
 decide +kernel
def pointBounds16832 : List (Nat × Nat × Nat) := [(2210201600,97777791476677,97778170485867)]
theorem point_links_checked16832 : (cuts16832.take 1).map (fun c => (2210136065-1+2*2^9*c.k,97777405083218+c.lower,97777784092161+c.upper)) = pointBounds16832 := by
 decide +kernel
def cuts16833 : List PrefixCut := [⟨4,24960344,24960360⟩,
⟨72,434252259,434252533⟩,
⟨128,770946957,770947443⟩]
theorem checked16833 : checkPrefixCuts (2^48) 2210267137 9 Manual.Count131072.C016833.packed 128 cuts16833 = true := by
 decide +kernel
def pointBounds16833 : List (Nat × Nat × Nat) := [(2210271232,97778209696024,97778588705476),(2210340864,97778618987939,97778997997649)]
theorem point_links_checked16833 : (cuts16833.take 2).map (fun c => (2210267137-1+2*2^9*c.k,97778184735680+c.lower,97778563745116+c.upper)) = pointBounds16833 := by
 decide +kernel
def cuts16834 : List PrefixCut := [⟨12,69400791,69400835⟩,
⟨80,485161129,485161438⟩,
⟨128,782488658,782489151⟩]
theorem checked16834 : checkPrefixCuts (2^48) 2210398209 9 Manual.Count131072.C016834.packed 128 cuts16834 = true := by
 decide +kernel
def pointBounds16834 : List (Nat × Nat × Nat) := [(2210410496,97779025083428,97779404093394),(2210480128,97779440843766,97779819853997)]
theorem point_links_checked16834 : (cuts16834.take 2).map (fun c => (2210398209-1+2*2^9*c.k,97778955682637+c.lower,97779334692559+c.upper)) = pointBounds16834 := by
 decide +kernel
def cuts16835 : List PrefixCut := [⟨20,119183794,119183869⟩,
⟨88,525750168,525750495⟩,
⟨128,766908127,766908608⟩]
theorem checked16835 : checkPrefixCuts (2^48) 2210529281 9 Manual.Count131072.C016835.packed 128 cuts16835 = true := by
 decide +kernel
def pointBounds16835 : List (Nat × Nat × Nat) := [(2210549760,97779857355089,97780236365579),(2210619392,97780263921463,97780642932205)]
theorem point_links_checked16835 : (cuts16835.take 2).map (fun c => (2210529281-1+2*2^9*c.k,97779738171295+c.lower,97780117181710+c.upper)) = pointBounds16835 := by
 decide +kernel
def cuts16836 : List PrefixCut := [⟨28,165013626,165013729⟩,
⟨96,577920507,577920868⟩,
⟨128,777302935,777303420⟩]
theorem checked16836 : checkPrefixCuts (2^48) 2210660353 9 Manual.Count131072.C016836.packed 128 cuts16836 = true := by
 decide +kernel
def pointBounds16836 : List (Nat × Nat × Nat) := [(2210689024,97780670093048,97781049104047),(2210758656,97781082999929,97781462011186)]
theorem point_links_checked16836 : (cuts16836.take 2).map (fun c => (2210660353-1+2*2^9*c.k,97780505079422+c.lower,97780884090318+c.upper)) = pointBounds16836 := by
 decide +kernel
def cuts16837 : List PrefixCut := [⟨36,213002235,213002373⟩,
⟨104,626774317,626774709⟩,
⟨128,768726936,768727419⟩]
theorem checked16837 : checkPrefixCuts (2^48) 2210791425 9 Manual.Count131072.C016837.packed 128 cuts16837 = true := by
 decide +kernel
def pointBounds16837 : List (Nat × Nat × Nat) := [(2210828288,97781495384592,97781874396111),(2210897920,97781909156674,97782288168447)]
theorem point_links_checked16837 : (cuts16837.take 2).map (fun c => (2210791425-1+2*2^9*c.k,97781282382357+c.lower,97781661393738+c.upper)) = pointBounds16837 := by
 decide +kernel
def cuts16838 : List PrefixCut := [⟨44,263913177,263913342⟩,
⟨112,682369566,682369994⟩,
⟨128,782303197,782303687⟩]
theorem checked16838 : checkPrefixCuts (2^48) 2210922497 9 Manual.Count131072.C016838.packed 128 cuts16838 = true := by
 decide +kernel
def pointBounds16838 : List (Nat × Nat × Nat) := [(2210967552,97782315022470,97782694034499),(2211037184,97782733478859,97783112491151)]
theorem point_links_checked16838 : (cuts16838.take 2).map (fun c => (2210922497-1+2*2^9*c.k,97782051109293+c.lower,97782430121157+c.upper)) = pointBounds16838 := by
 decide +kernel
def cuts16839 : List PrefixCut := [⟨52,311126003,311126204⟩,
⟨120,724973297,724973755⟩,
⟨128,771563706,771564193⟩]
theorem checked16839 : checkPrefixCuts (2^48) 2211053569 9 Manual.Count131072.C016839.packed 128 cuts16839 = true := by
 decide +kernel
def pointBounds16839 : List (Nat × Nat × Nat) := [(2211106816,97783144538493,97783523551048),(2211176448,97783558385787,97783937398599)]
theorem point_links_checked16839 : (cuts16839.take 2).map (fun c => (2211053569-1+2*2^9*c.k,97782833412490+c.lower,97783212424844+c.upper)) = pointBounds16839 := by
 decide +kernel
def cuts16840 : List PrefixCut := [⟨60,359351522,359351749⟩,
⟨128,767953786,767954269⟩]
theorem checked16840 : checkPrefixCuts (2^48) 2211184641 9 Manual.Count131072.C016840.packed 128 cuts16840 = true := by
 decide +kernel
def pointBounds16840 : List (Nat × Nat × Nat) := [(2211246080,97783964327718,97784343340786),(2211315712,97784372929982,97784751943306)]
theorem point_links_checked16840 : (cuts16840.take 2).map (fun c => (2211184641-1+2*2^9*c.k,97783604976196+c.lower,97783983989037+c.upper)) = pointBounds16840 := by
 decide +kernel
def cuts16841 : List PrefixCut := [⟨68,408843979,408844240⟩,
⟨128,765235396,765235884⟩]
theorem checked16841 : checkPrefixCuts (2^48) 2211315713 9 Manual.Count131072.C016841.packed 128 cuts16841 = true := by
 decide +kernel
def pointBounds16841 : List (Nat × Nat × Nat) := [(2211385344,97784781773961,97785160787546)]
theorem point_links_checked16841 : (cuts16841.take 1).map (fun c => (2211315713-1+2*2^9*c.k,97784372929982+c.lower,97784751943306+c.upper)) = pointBounds16841 := by
 decide +kernel
def cuts16842 : List PrefixCut := [⟨8,45821031,45821061⟩,
⟨76,464312470,464312756⟩,
⟨128,777281378,777281860⟩]
theorem checked16842 : checkPrefixCuts (2^48) 2211446785 9 Manual.Count131072.C016842.packed 128 cuts16842 = true := by
 decide +kernel
def pointBounds16842 : List (Nat × Nat × Nat) := [(2211454976,97785183986409,97785563000251),(2211524608,97785602477848,97785981491946)]
theorem point_links_checked16842 : (cuts16842.take 2).map (fun c => (2211446785-1+2*2^9*c.k,97785138165378+c.lower,97785517179190+c.upper)) = pointBounds16842 := by
 decide +kernel
def cuts16843 : List PrefixCut := [⟨16,96854646,96854707⟩,
⟨84,510483347,510483665⟩,
⟨128,777871478,777871967⟩]
theorem checked16843 : checkPrefixCuts (2^48) 2211577857 9 Manual.Count131072.C016843.packed 128 cuts16843 = true := by
 decide +kernel
def pointBounds16843 : List (Nat × Nat × Nat) := [(2211594240,97786012301402,97786391315757),(2211663872,97786425930103,97786804944715)]
theorem point_links_checked16843 : (cuts16843.take 2).map (fun c => (2211577857-1+2*2^9*c.k,97785915446756+c.lower,97786294461050+c.upper)) = pointBounds16843 := by
 decide +kernel
def cuts16844 : List PrefixCut := [⟨24,146354851,146354940⟩,
⟨92,557030520,557030863⟩,
⟨128,771335207,771335686⟩]
theorem checked16844 : checkPrefixCuts (2^48) 2211708929 9 Manual.Count131072.C016844.packed 128 cuts16844 = true := by
 decide +kernel
def pointBounds16844 : List (Nat × Nat × Nat) := [(2211733504,97786839673085,97787218687957),(2211803136,97787250348754,97787629363880)]
theorem point_links_checked16844 : (cuts16844.take 2).map (fun c => (2211708929-1+2*2^9*c.k,97786693318234+c.lower,97787072333017+c.upper)) = pointBounds16844 := by
 decide +kernel
def cuts16845 : List PrefixCut := [⟨32,196485302,196485421⟩,
⟨100,611716189,611716568⟩,
⟨128,778797433,778797917⟩]
theorem checked16845 : checkPrefixCuts (2^48) 2211840001 9 Manual.Count131072.C016845.packed 128 cuts16845 = true := by
 decide +kernel
def pointBounds16845 : List (Nat × Nat × Nat) := [(2211872768,97787661138743,97788040154124),(2211942400,97788076369630,97788455385271)]
theorem point_links_checked16845 : (cuts16845.take 2).map (fun c => (2211840001-1+2*2^9*c.k,97787464653441+c.lower,97787843668703+c.upper)) = pointBounds16845 := by
 decide +kernel
def cuts16846 : List PrefixCut := [⟨40,239483612,239483761⟩,
⟨108,643999769,644000170⟩,
⟨128,768571414,768571895⟩]
theorem checked16846 : checkPrefixCuts (2^48) 2211971073 9 Manual.Count131072.C016846.packed 128 cuts16846 = true := by
 decide +kernel
def pointBounds16846 : List (Nat × Nat × Nat) := [(2212012032,97788482934486,97788861950381),(2212081664,97788887450643,97789266466790)]
theorem point_links_checked16846 : (cuts16846.take 2).map (fun c => (2211971073-1+2*2^9*c.k,97788243450874+c.lower,97788622466620+c.upper)) = pointBounds16846 := by
 decide +kernel
def cuts16847 : List PrefixCut := [⟨48,294183009,294183194⟩,
⟨116,705035561,705036002⟩,
⟨128,776796656,776797143⟩]
theorem checked16847 : checkPrefixCuts (2^48) 2212102145 9 Manual.Count131072.C016847.packed 128 cuts16847 = true := by
 decide +kernel
def pointBounds16847 : List (Nat × Nat × Nat) := [(2212151296,97789306205297,97789685221709),(2212220928,97789717057849,97790096074517)]
theorem point_links_checked16847 : (cuts16847.take 2).map (fun c => (2212102145-1+2*2^9*c.k,97789012022288+c.lower,97789391038515+c.upper)) = pointBounds16847 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000213
