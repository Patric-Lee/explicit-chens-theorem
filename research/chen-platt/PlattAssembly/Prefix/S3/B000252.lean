import PlattAssemblyKernel
import PlattCertificates.Count131072.C028064
import PlattCertificates.Count131072.C028065
import PlattCertificates.Count131072.C028066
import PlattCertificates.Count131072.C028067
import PlattCertificates.Count131072.C028068
import PlattCertificates.Count131072.C028069
import PlattCertificates.Count131072.C028070
import PlattCertificates.Count131072.C028071
import PlattCertificates.Count131072.C028072
import PlattCertificates.Count131072.C028073
import PlattCertificates.Count131072.C028074
import PlattCertificates.Count131072.C028075
import PlattCertificates.Count131072.C028076
import PlattCertificates.Count131072.C028077
import PlattCertificates.Count131072.C028078
import PlattCertificates.Count131072.C028079
import PlattCertificates.Count131072.C028080
import PlattCertificates.Count131072.C028081
import PlattCertificates.Count131072.C028082
import PlattCertificates.Count131072.C028083
import PlattCertificates.Count131072.C028084
import PlattCertificates.Count131072.C028085
import PlattCertificates.Count131072.C028086
import PlattCertificates.Count131072.C028087
import PlattCertificates.Count131072.C028088
import PlattCertificates.Count131072.C028089
import PlattCertificates.Count131072.C028090
import PlattCertificates.Count131072.C028091
import PlattCertificates.Count131072.C028092
import PlattCertificates.Count131072.C028093
import PlattCertificates.Count131072.C028094
import PlattCertificates.Count131072.C028095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000252
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28064 : List PrefixCut := [⟨70,249418710,249418848⟩,
⟨128,452282787,452283043⟩]
theorem checked28064 : checkPrefixCuts (2^48) 3682336769 9 Manual.Count131072.C028064.packed 128 cuts28064 = true := by
 decide +kernel
def pointBounds28064 : List (Nat × Nat × Nat) := [(3682408448,104377983200946,104378366045912)]
theorem point_links_checked28064 : (cuts28064.take 1).map (fun c => (3682336769-1+2*2^9*c.k,104377733782236+c.lower,104378116627064+c.upper)) = pointBounds28064 := by
 decide +kernel
def cuts28065 : List PrefixCut := [⟨55,194300064,194300177⟩,
⟨128,451349417,451349678⟩]
theorem checked28065 : checkPrefixCuts (2^48) 3682467841 9 Manual.Count131072.C028065.packed 128 cuts28065 = true := by
 decide +kernel
def pointBounds28065 : List (Nat × Nat × Nat) := [(3682524160,104378380365087,104378763210284)]
theorem point_links_checked28065 : (cuts28065.take 1).map (fun c => (3682467841-1+2*2^9*c.k,104378186065023+c.lower,104378568910107+c.upper)) = pointBounds28065 := by
 decide +kernel
def cuts28066 : List PrefixCut := [⟨40,144688317,144688399⟩,
⟨128,451715571,451715821⟩]
theorem checked28066 : checkPrefixCuts (2^48) 3682598913 9 Manual.Count131072.C028066.packed 128 cuts28066 = true := by
 decide +kernel
def pointBounds28066 : List (Nat × Nat × Nat) := [(3682639872,104378782102757,104379164948184)]
theorem point_links_checked28066 : (cuts28066.take 1).map (fun c => (3682598913-1+2*2^9*c.k,104378637414440+c.lower,104379020259785+c.upper)) = pointBounds28066 := by
 decide +kernel
def cuts28067 : List PrefixCut := [⟨25,88430415,88430465⟩,
⟨128,452157997,452158247⟩]
theorem checked28067 : checkPrefixCuts (2^48) 3682729985 9 Manual.Count131072.C028067.packed 128 cuts28067 = true := by
 decide +kernel
def pointBounds28067 : List (Nat × Nat × Nat) := [(3682755584,104379177560426,104379560406071)]
theorem point_links_checked28067 : (cuts28067.take 1).map (fun c => (3682729985-1+2*2^9*c.k,104379089130011+c.lower,104379471975606+c.upper)) = pointBounds28067 := by
 decide +kernel
def cuts28068 : List PrefixCut := [⟨10,34927697,34927714⟩,
⟨123,439378847,439379087⟩,
⟨128,457568154,457568404⟩]
theorem checked28068 : checkPrefixCuts (2^48) 3682861057 9 Manual.Count131072.C028068.packed 128 cuts28068 = true := by
 decide +kernel
def pointBounds28068 : List (Nat × Nat × Nat) := [(3682871296,104379576215705,104379959061567),(3682987008,104379980666855,104380363512940)]
theorem point_links_checked28068 : (cuts28068.take 2).map (fun c => (3682861057-1+2*2^9*c.k,104379541288008+c.lower,104379924133853+c.upper)) = pointBounds28068 := by
 decide +kernel
def cuts28069 : List PrefixCut := [⟨108,385637805,385638022⟩,
⟨128,455870630,455870887⟩]
theorem checked28069 : checkPrefixCuts (2^48) 3682992129 9 Manual.Count131072.C028069.packed 128 cuts28069 = true := by
 decide +kernel
def pointBounds28069 : List (Nat × Nat × Nat) := [(3683102720,104380384493967,104380767340279)]
theorem point_links_checked28069 : (cuts28069.take 1).map (fun c => (3682992129-1+2*2^9*c.k,104379998856162+c.lower,104380381702257+c.upper)) = pointBounds28069 := by
 decide +kernel
def cuts28070 : List PrefixCut := [⟨93,326092245,326092425⟩,
⟨128,450581290,450581540⟩]
theorem checked28070 : checkPrefixCuts (2^48) 3683123201 9 Manual.Count131072.C028070.packed 128 cuts28070 = true := by
 decide +kernel
def pointBounds28070 : List (Nat × Nat × Nat) := [(3683218432,104380780819037,104381163665569)]
theorem point_links_checked28070 : (cuts28070.take 1).map (fun c => (3683123201-1+2*2^9*c.k,104380454726792+c.lower,104380837573144+c.upper)) = pointBounds28070 := by
 decide +kernel
def cuts28071 : List PrefixCut := [⟨78,275720974,275721132⟩,
⟨128,453392784,453393045⟩]
theorem checked28071 : checkPrefixCuts (2^48) 3683254273 9 Manual.Count131072.C028071.packed 128 cuts28071 = true := by
 decide +kernel
def pointBounds28071 : List (Nat × Nat × Nat) := [(3683334144,104381181029056,104381563875816)]
theorem point_links_checked28071 : (cuts28071.take 1).map (fun c => (3683254273-1+2*2^9*c.k,104380905308082+c.lower,104381288154684+c.upper)) = pointBounds28071 := by
 decide +kernel
def cuts28072 : List PrefixCut := [⟨63,221073716,221073843⟩,
⟨128,451160545,451160802⟩]
theorem checked28072 : checkPrefixCuts (2^48) 3683385345 9 Manual.Count131072.C028072.packed 128 cuts28072 = true := by
 decide +kernel
def pointBounds28072 : List (Nat × Nat × Nat) := [(3683449856,104381579774582,104381962621572)]
theorem point_links_checked28072 : (cuts28072.take 1).map (fun c => (3683385345-1+2*2^9*c.k,104381358700866+c.lower,104381741547729+c.upper)) = pointBounds28072 := by
 decide +kernel
def cuts28073 : List PrefixCut := [⟨48,170021639,170021730⟩,
⟨128,449616255,449616504⟩]
theorem checked28073 : checkPrefixCuts (2^48) 3683516417 9 Manual.Count131072.C028073.packed 128 cuts28073 = true := by
 decide +kernel
def pointBounds28073 : List (Nat × Nat × Nat) := [(3683565568,104381979883050,104382362730261)]
theorem point_links_checked28073 : (cuts28073.take 1).map (fun c => (3683516417-1+2*2^9*c.k,104381809861411+c.lower,104382192708531+c.upper)) = pointBounds28073 := by
 decide +kernel
def cuts28074 : List PrefixCut := [⟨33,114770304,114770369⟩,
⟨128,455178198,455178452⟩]
theorem checked28074 : checkPrefixCuts (2^48) 3683647489 9 Manual.Count131072.C028074.packed 128 cuts28074 = true := by
 decide +kernel
def pointBounds28074 : List (Nat × Nat × Nat) := [(3683681280,104382374247970,104382757095404)]
theorem point_links_checked28074 : (cuts28074.take 1).map (fun c => (3683647489-1+2*2^9*c.k,104382259477666+c.lower,104382642325035+c.upper)) = pointBounds28074 := by
 decide +kernel
def cuts28075 : List PrefixCut := [⟨18,64260050,64260087⟩,
⟨128,454092375,454092634⟩]
theorem checked28075 : checkPrefixCuts (2^48) 3683778561 9 Manual.Count131072.C028075.packed 128 cuts28075 = true := by
 decide +kernel
def pointBounds28075 : List (Nat × Nat × Nat) := [(3683796992,104382778915914,104383161763574)]
theorem point_links_checked28075 : (cuts28075.take 1).map (fun c => (3683778561-1+2*2^9*c.k,104382714655864+c.lower,104383097503487+c.upper)) = pointBounds28075 := by
 decide +kernel
def cuts28076 : List PrefixCut := [⟨3,11078948,11078954⟩,
⟨116,414116947,414117182⟩,
⟨128,457285196,457285455⟩]
theorem checked28076 : checkPrefixCuts (2^48) 3683909633 9 Manual.Count131072.C028076.packed 128 cuts28076 = true := by
 decide +kernel
def pointBounds28076 : List (Nat × Nat × Nat) := [(3683912704,104383179827187,104383562675075),(3684028416,104383582865186,104383965713303)]
theorem point_links_checked28076 : (cuts28076.take 2).map (fun c => (3683909633-1+2*2^9*c.k,104383168748239+c.lower,104383551596121+c.upper)) = pointBounds28076 := by
 decide +kernel
def cuts28077 : List PrefixCut := [⟨101,353668428,353668632⟩,
⟨128,450621839,450622097⟩]
theorem checked28077 : checkPrefixCuts (2^48) 3684040705 9 Manual.Count131072.C028077.packed 128 cuts28077 = true := by
 decide +kernel
def pointBounds28077 : List (Nat × Nat × Nat) := [(3684144128,104383979701863,104384362550208)]
theorem point_links_checked28077 : (cuts28077.take 1).map (fun c => (3684040705-1+2*2^9*c.k,104383626033435+c.lower,104384008881576+c.upper)) = pointBounds28077 := by
 decide +kernel
def cuts28078 : List PrefixCut := [⟨86,303308917,303309089⟩,
⟨128,451293530,451293781⟩]
theorem checked28078 : checkPrefixCuts (2^48) 3684171777 9 Manual.Count131072.C028078.packed 128 cuts28078 = true := by
 decide +kernel
def pointBounds28078 : List (Nat × Nat × Nat) := [(3684259840,104384379964191,104384762812762)]
theorem point_links_checked28078 : (cuts28078.take 1).map (fun c => (3684171777-1+2*2^9*c.k,104384076655274+c.lower,104384459503673+c.upper)) = pointBounds28078 := by
 decide +kernel
def cuts28079 : List PrefixCut := [⟨71,252417888,252418028⟩,
⟨128,453111002,453111257⟩]
theorem checked28079 : checkPrefixCuts (2^48) 3684302849 9 Manual.Count131072.C028079.packed 128 cuts28079 = true := by
 decide +kernel
def pointBounds28079 : List (Nat × Nat × Nat) := [(3684375552,104384780366692,104385163215482)]
theorem point_links_checked28079 : (cuts28079.take 1).map (fun c => (3684302849-1+2*2^9*c.k,104384527948804+c.lower,104384910797454+c.upper)) = pointBounds28079 := by
 decide +kernel
def cuts28080 : List PrefixCut := [⟨56,198856438,198856550⟩,
⟨128,452407282,452407539⟩]
theorem checked28080 : checkPrefixCuts (2^48) 3684433921 9 Manual.Count131072.C028080.packed 128 cuts28080 = true := by
 decide +kernel
def pointBounds28080 : List (Nat × Nat × Nat) := [(3684491264,104385179916244,104385562765261)]
theorem point_links_checked28080 : (cuts28080.take 1).map (fun c => (3684433921-1+2*2^9*c.k,104384981059806+c.lower,104385363908711+c.upper)) = pointBounds28080 := by
 decide +kernel
def cuts28081 : List PrefixCut := [⟨41,146597305,146597387⟩,
⟨128,460717932,460718186⟩]
theorem checked28081 : checkPrefixCuts (2^48) 3684564993 9 Manual.Count131072.C028081.packed 128 cuts28081 = true := by
 decide +kernel
def pointBounds28081 : List (Nat × Nat × Nat) := [(3684606976,104385580064393,104385962913637)]
theorem point_links_checked28081 : (cuts28081.take 1).map (fun c => (3684564993-1+2*2^9*c.k,104385433467088+c.lower,104385816316250+c.upper)) = pointBounds28081 := by
 decide +kernel
def cuts28082 : List PrefixCut := [⟨26,89758234,89758286⟩,
⟨128,454131994,454132250⟩]
theorem checked28082 : checkPrefixCuts (2^48) 3684696065 9 Manual.Count131072.C028082.packed 128 cuts28082 = true := by
 decide +kernel
def pointBounds28082 : List (Nat × Nat × Nat) := [(3684722688,104385983943254,104386366792722)]
theorem point_links_checked28082 : (cuts28082.take 1).map (fun c => (3684696065-1+2*2^9*c.k,104385894185020+c.lower,104386277034436+c.upper)) = pointBounds28082 := by
 decide +kernel
def cuts28083 : List PrefixCut := [⟨11,38499264,38499284⟩,
⟨124,435172380,435172626⟩,
⟨128,448616117,448616371⟩]
theorem checked28083 : checkPrefixCuts (2^48) 3684827137 9 Manual.Count131072.C028083.packed 128 cuts28083 = true := by
 decide +kernel
def pointBounds28083 : List (Nat × Nat × Nat) := [(3684838400,104386386816278,104386769665970),(3684954112,104386783489394,104387166339312)]
theorem point_links_checked28083 : (cuts28083.take 2).map (fun c => (3684827137-1+2*2^9*c.k,104386348317014+c.lower,104386731166686+c.upper)) = pointBounds28083 := by
 decide +kernel
def cuts28084 : List PrefixCut := [⟨109,384362639,384362857⟩,
⟨128,452495665,452495919⟩]
theorem checked28084 : checkPrefixCuts (2^48) 3684958209 9 Manual.Count131072.C028084.packed 128 cuts28084 = true := by
 decide +kernel
def pointBounds28084 : List (Nat × Nat × Nat) := [(3685069824,104387181295770,104387564145914)]
theorem point_links_checked28084 : (cuts28084.take 1).map (fun c => (3684958209-1+2*2^9*c.k,104386796933131+c.lower,104387179783057+c.upper)) = pointBounds28084 := by
 decide +kernel
def cuts28085 : List PrefixCut := [⟨94,336000505,336000699⟩,
⟨128,456680526,456680787⟩]
theorem checked28085 : checkPrefixCuts (2^48) 3685089281 9 Manual.Count131072.C028085.packed 128 cuts28085 = true := by
 decide +kernel
def pointBounds28085 : List (Nat × Nat × Nat) := [(3685185536,104387585429301,104387968279675)]
theorem point_links_checked28085 : (cuts28085.take 1).map (fun c => (3685089281-1+2*2^9*c.k,104387249428796+c.lower,104387632278976+c.upper)) = pointBounds28085 := by
 decide +kernel
def cuts28086 : List PrefixCut := [⟨79,283899134,283899292⟩,
⟨128,456206083,456206336⟩]
theorem checked28086 : checkPrefixCuts (2^48) 3685220353 9 Manual.Count131072.C028086.packed 128 cuts28086 = true := by
 decide +kernel
def pointBounds28086 : List (Nat × Nat × Nat) := [(3685301248,104387990008456,104388372859055)]
theorem point_links_checked28086 : (cuts28086.take 1).map (fun c => (3685220353-1+2*2^9*c.k,104387706109322+c.lower,104388088959763+c.upper)) = pointBounds28086 := by
 decide +kernel
def cuts28087 : List PrefixCut := [⟨64,228669742,228669871⟩,
⟨128,452065575,452065829⟩]
theorem checked28087 : checkPrefixCuts (2^48) 3685351425 9 Manual.Count131072.C028087.packed 128 cuts28087 = true := by
 decide +kernel
def pointBounds28087 : List (Nat × Nat × Nat) := [(3685416960,104388390985147,104388773835970)]
theorem point_links_checked28087 : (cuts28087.take 1).map (fun c => (3685351425-1+2*2^9*c.k,104388162315405+c.lower,104388545166099+c.upper)) = pointBounds28087 := by
 decide +kernel
def cuts28088 : List PrefixCut := [⟨49,177033631,177033730⟩,
⟨128,453653271,453653529⟩]
theorem checked28088 : checkPrefixCuts (2^48) 3685482497 9 Manual.Count131072.C028088.packed 128 cuts28088 = true := by
 decide +kernel
def pointBounds28088 : List (Nat × Nat × Nat) := [(3685532672,104388791414611,104389174265658)]
theorem point_links_checked28088 : (cuts28088.take 1).map (fun c => (3685482497-1+2*2^9*c.k,104388614380980+c.lower,104388997231928+c.upper)) = pointBounds28088 := by
 decide +kernel
def cuts28089 : List PrefixCut := [⟨34,118298499,118298563⟩,
⟨128,453255227,453255478⟩]
theorem checked28089 : checkPrefixCuts (2^48) 3685613569 9 Manual.Count131072.C028089.packed 128 cuts28089 = true := by
 decide +kernel
def pointBounds28089 : List (Nat × Nat × Nat) := [(3685648384,104389186332750,104389569184020)]
theorem point_links_checked28089 : (cuts28089.take 1).map (fun c => (3685613569-1+2*2^9*c.k,104389068034251+c.lower,104389450885457+c.upper)) = pointBounds28089 := by
 decide +kernel
def cuts28090 : List PrefixCut := [⟨19,67585968,67586006⟩,
⟨128,444609676,444609929⟩]
theorem checked28090 : checkPrefixCuts (2^48) 3685744641 9 Manual.Count131072.C028090.packed 128 cuts28090 = true := by
 decide +kernel
def pointBounds28090 : List (Nat × Nat × Nat) := [(3685764096,104389588875446,104389971726941)]
theorem point_links_checked28090 : (cuts28090.take 1).map (fun c => (3685744641-1+2*2^9*c.k,104389521289478+c.lower,104389904140935+c.upper)) = pointBounds28090 := by
 decide +kernel
def cuts28091 : List PrefixCut := [⟨4,13516741,13516748⟩,
⟨117,416797823,416798056⟩,
⟨128,458492136,458492392⟩]
theorem checked28091 : checkPrefixCuts (2^48) 3685875713 9 Manual.Count131072.C028091.packed 128 cuts28091 = true := by
 decide +kernel
def pointBounds28091 : List (Nat × Nat × Nat) := [(3685879808,104389979415895,104390362267612),(3685995520,104390382696977,104390765548920)]
theorem point_links_checked28091 : (cuts28091.take 2).map (fun c => (3685875713-1+2*2^9*c.k,104389965899154+c.lower,104390348750864+c.upper)) = pointBounds28091 := by
 decide +kernel
def cuts28092 : List PrefixCut := [⟨102,366384946,366385148⟩,
⟨128,455955997,455956247⟩]
theorem checked28092 : checkPrefixCuts (2^48) 3686006785 9 Manual.Count131072.C028092.packed 128 cuts28092 = true := by
 decide +kernel
def pointBounds28092 : List (Nat × Nat × Nat) := [(3686111232,104390790776236,104391173628404)]
theorem point_links_checked28092 : (cuts28092.take 1).map (fun c => (3686006785-1+2*2^9*c.k,104390424391290+c.lower,104390807243256+c.upper)) = pointBounds28092 := by
 decide +kernel
def cuts28093 : List PrefixCut := [⟨87,307499561,307499734⟩,
⟨128,453114487,453114742⟩]
theorem checked28093 : checkPrefixCuts (2^48) 3686137857 9 Manual.Count131072.C028093.packed 128 cuts28093 = true := by
 decide +kernel
def pointBounds28093 : List (Nat × Nat × Nat) := [(3686226944,104391187846848,104391570699237)]
theorem point_links_checked28093 : (cuts28093.take 1).map (fun c => (3686137857-1+2*2^9*c.k,104390880347287+c.lower,104391263199503+c.upper)) = pointBounds28093 := by
 decide +kernel
def cuts28094 : List PrefixCut := [⟨72,251672385,251672529⟩,
⟨128,449967741,449967998⟩]
theorem checked28094 : checkPrefixCuts (2^48) 3686268929 9 Manual.Count131072.C028094.packed 128 cuts28094 = true := by
 decide +kernel
def pointBounds28094 : List (Nat × Nat × Nat) := [(3686342656,104391585134159,104391967986774)]
theorem point_links_checked28094 : (cuts28094.take 1).map (fun c => (3686268929-1+2*2^9*c.k,104391333461774+c.lower,104391716314245+c.upper)) = pointBounds28094 := by
 decide +kernel
def cuts28095 : List PrefixCut := [⟨57,201040983,201041096⟩,
⟨128,450867992,450868245⟩]
theorem checked28095 : checkPrefixCuts (2^48) 3686400001 9 Manual.Count131072.C028095.packed 128 cuts28095 = true := by
 decide +kernel
def pointBounds28095 : List (Nat × Nat × Nat) := [(3686458368,104391984470498,104392367323339)]
theorem point_links_checked28095 : (cuts28095.take 1).map (fun c => (3686400001-1+2*2^9*c.k,104391783429515+c.lower,104392166282243+c.upper)) = pointBounds28095 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000252
