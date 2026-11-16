import PlattAssemblyKernel
import PlattCertificates.Count131072.C012816
import PlattCertificates.Count131072.C012817
import PlattCertificates.Count131072.C012818
import PlattCertificates.Count131072.C012819
import PlattCertificates.Count131072.C012820
import PlattCertificates.Count131072.C012821
import PlattCertificates.Count131072.C012822
import PlattCertificates.Count131072.C012823
import PlattCertificates.Count131072.C012824
import PlattCertificates.Count131072.C012825
import PlattCertificates.Count131072.C012826
import PlattCertificates.Count131072.C012827
import PlattCertificates.Count131072.C012828
import PlattCertificates.Count131072.C012829
import PlattCertificates.Count131072.C012830
import PlattCertificates.Count131072.C012831
import PlattCertificates.Count131072.C012832
import PlattCertificates.Count131072.C012833
import PlattCertificates.Count131072.C012834
import PlattCertificates.Count131072.C012835
import PlattCertificates.Count131072.C012836
import PlattCertificates.Count131072.C012837
import PlattCertificates.Count131072.C012838
import PlattCertificates.Count131072.C012839
import PlattCertificates.Count131072.C012840
import PlattCertificates.Count131072.C012841
import PlattCertificates.Count131072.C012842
import PlattCertificates.Count131072.C012843
import PlattCertificates.Count131072.C012844
import PlattCertificates.Count131072.C012845
import PlattCertificates.Count131072.C012846
import PlattCertificates.Count131072.C012847
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000088
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12816 : List PrefixCut := [⟨50,405885743,405886038⟩,
⟨102,832654500,832655107⟩,
⟨128,1045783029,1045783789⟩]
theorem checked12816 : checkPrefixCuts (2^48) 1683750913 9 Manual.Count131072.C012816.packed 128 cuts12816 = true := by
 decide +kernel
def pointBounds12816 : List (Nat × Nat × Nat) := [(1683802112,94196529144797,94196905732794),(1683855360,94196955913554,94197332501863)]
theorem point_links_checked12816 : (cuts12816.take 2).map (fun c => (1683750913-1+2*2^9*c.k,94196123259054+c.lower,94196499846756+c.upper)) = pointBounds12816 := by
 decide +kernel
def cuts12817 : List PrefixCut := [⟨26,208444755,208444910⟩,
⟨78,634183526,634183992⟩,
⟨128,1034335430,1034336188⟩]
theorem checked12817 : checkPrefixCuts (2^48) 1683881985 9 Manual.Count131072.C012817.packed 128 cuts12817 = true := by
 decide +kernel
def pointBounds12817 : List (Nat × Nat × Nat) := [(1683908608,94197377486838,94197754075455),(1683961856,94197803225609,94198179814537)]
theorem point_links_checked12817 : (cuts12817.take 2).map (fun c => (1683881985-1+2*2^9*c.k,94197169042083+c.lower,94197545630545+c.upper)) = pointBounds12817 := by
 decide +kernel
def cuts12818 : List PrefixCut := [⟨2,14374488,14374499⟩,
⟨54,432899282,432899602⟩,
⟨106,842719645,842720263⟩,
⟨128,1015201329,1015202074⟩]
theorem checked12818 : checkPrefixCuts (2^48) 1684013057 9 Manual.Count131072.C012818.packed 128 cuts12818 = true := by
 decide +kernel
def pointBounds12818 : List (Nat × Nat × Nat) := [(1684015104,94198217752001,94198594341232),(1684068352,94198636276795,94199012866335),(1684121600,94199046097158,94199422686996)]
theorem point_links_checked12818 : (cuts12818.take 3).map (fun c => (1684013057-1+2*2^9*c.k,94198203377513+c.lower,94198579966733+c.upper)) = pointBounds12818 := by
 decide +kernel
def cuts12819 : List PrefixCut := [⟨30,249024796,249024980⟩,
⟨82,669014015,669014504⟩,
⟨128,1045539029,1045539794⟩]
theorem checked12819 : checkPrefixCuts (2^48) 1684144129 9 Manual.Count131072.C012819.packed 128 cuts12819 = true := by
 decide +kernel
def pointBounds12819 : List (Nat × Nat × Nat) := [(1684174848,94199467603638,94199844193787),(1684228096,94199887592857,94200264183311)]
theorem point_links_checked12819 : (cuts12819.take 2).map (fun c => (1684144129-1+2*2^9*c.k,94199218578842+c.lower,94199595168807+c.upper)) = pointBounds12819 := by
 decide +kernel
def cuts12820 : List PrefixCut := [⟨6,47628906,47628942⟩,
⟨58,465084752,465085094⟩,
⟨110,877179969,877180612⟩,
⟨128,1022563239,1022563990⟩]
theorem checked12820 : checkPrefixCuts (2^48) 1684275201 9 Manual.Count131072.C012820.packed 128 cuts12820 = true := by
 decide +kernel
def pointBounds12820 : List (Nat × Nat × Nat) := [(1684281344,94200311746777,94200688337543),(1684334592,94200729202623,94201105793695),(1684387840,94201141297840,94201517889213)]
theorem point_links_checked12820 : (cuts12820.take 3).map (fun c => (1684275201-1+2*2^9*c.k,94200264117871+c.lower,94200640708601+c.upper)) = pointBounds12820 := by
 decide +kernel
def cuts12821 : List PrefixCut := [⟨34,267701517,267701713⟩,
⟨86,690966329,690966830⟩,
⟨128,1035517117,1035517871⟩]
theorem checked12821 : checkPrefixCuts (2^48) 1684406273 9 Manual.Count131072.C012821.packed 128 cuts12821 = true := by
 decide +kernel
def pointBounds12821 : List (Nat × Nat × Nat) := [(1684441088,94201554382627,94201930974304),(1684494336,94201977647439,94202354239421)]
theorem point_links_checked12821 : (cuts12821.take 2).map (fun c => (1684406273-1+2*2^9*c.k,94201286681110+c.lower,94201663272591+c.upper)) = pointBounds12821 := by
 decide +kernel
def cuts12822 : List PrefixCut := [⟨10,82042555,82042614⟩,
⟨62,504612259,504612623⟩,
⟨114,923158575,923159245⟩,
⟨128,1035938247,1035939001⟩]
theorem checked12822 : checkPrefixCuts (2^48) 1684537345 9 Manual.Count131072.C012822.packed 128 cuts12822 = true := by
 decide +kernel
def pointBounds12822 : List (Nat × Nat × Nat) := [(1684547584,94202404240782,94202780833076),(1684600832,94202826810486,94203203403085),(1684654080,94203245356802,94203621949707)]
theorem point_links_checked12822 : (cuts12822.take 3).map (fun c => (1684537345-1+2*2^9*c.k,94202322198227+c.lower,94202698790462+c.upper)) = pointBounds12822 := by
 decide +kernel
def cuts12823 : List PrefixCut := [⟨38,314775652,314775877⟩,
⟨90,728116253,728116785⟩,
⟨128,1030845607,1030846358⟩]
theorem checked12823 : checkPrefixCuts (2^48) 1684668417 9 Manual.Count131072.C012823.packed 128 cuts12823 = true := by
 decide +kernel
def pointBounds12823 : List (Nat × Nat × Nat) := [(1684707328,94203672912126,94204049505340),(1684760576,94204086252727,94204462846248)]
theorem point_links_checked12823 : (cuts12823.take 2).map (fun c => (1684668417-1+2*2^9*c.k,94203358136474+c.lower,94203734729463+c.upper)) = pointBounds12823 := by
 decide +kernel
def cuts12824 : List PrefixCut := [⟨14,115777136,115777220⟩,
⟨66,523745554,523745935⟩,
⟨118,942058614,942059301⟩,
⟨128,1020240262,1020241006⟩]
theorem checked12824 : checkPrefixCuts (2^48) 1684799489 9 Manual.Count131072.C012824.packed 128 cuts12824 = true := by
 decide +kernel
def pointBounds12824 : List (Nat × Nat × Nat) := [(1684813824,94204504759217,94204881353041),(1684867072,94204912727635,94205289321756),(1684920320,94205331040695,94205707635122)]
theorem point_links_checked12824 : (cuts12824.take 3).map (fun c => (1684799489-1+2*2^9*c.k,94204388982081+c.lower,94204765575821+c.upper)) = pointBounds12824 := by
 decide +kernel
def cuts12825 : List PrefixCut := [⟨42,351644781,351645038⟩,
⟨94,770599650,770600213⟩,
⟨128,1051064933,1051065698⟩]
theorem checked12825 : checkPrefixCuts (2^48) 1684930561 9 Manual.Count131072.C012825.packed 128 cuts12825 = true := by
 decide +kernel
def pointBounds12825 : List (Nat × Nat × Nat) := [(1684973568,94205760867124,94206137461865),(1685026816,94206179821993,94206556417040)]
theorem point_links_checked12825 : (cuts12825.take 2).map (fun c => (1684930561-1+2*2^9*c.k,94205409222343+c.lower,94205785816827+c.upper)) = pointBounds12825 := by
 decide +kernel
def cuts12826 : List PrefixCut := [⟨18,145659219,145659327⟩,
⟨70,572438435,572438854⟩,
⟨122,987344738,987345459⟩,
⟨128,1037954402,1037955160⟩]
theorem checked12826 : checkPrefixCuts (2^48) 1685061633 9 Manual.Count131072.C012826.packed 128 cuts12826 = true := by
 decide +kernel
def pointBounds12826 : List (Nat × Nat × Nat) := [(1685080064,94206605946495,94206982541852),(1685133312,94207032725711,94207409321379),(1685186560,94207447632014,94207824227984)]
theorem point_links_checked12826 : (cuts12826.take 3).map (fun c => (1685061633-1+2*2^9*c.k,94206460287276+c.lower,94206836882525+c.upper)) = pointBounds12826 := by
 decide +kernel
def cuts12827 : List PrefixCut := [⟨46,370463535,370463807⟩,
⟨98,788684095,788684675⟩,
⟨128,1027351149,1027351906⟩]
theorem checked12827 : checkPrefixCuts (2^48) 1685192705 9 Manual.Count131072.C012827.packed 128 cuts12827 = true := by
 decide +kernel
def pointBounds12827 : List (Nat × Nat × Nat) := [(1685239808,94207868705213,94208245301492),(1685293056,94208286925773,94208663522360)]
theorem point_links_checked12827 : (cuts12827.take 2).map (fun c => (1685192705-1+2*2^9*c.k,94207498241678+c.lower,94207874837685+c.upper)) = pointBounds12827 := by
 decide +kernel
def cuts12828 : List PrefixCut := [⟨22,182713538,182713670⟩,
⟨74,593893227,593893659⟩,
⟨126,1011573137,1011573874⟩,
⟨128,1026937361,1026938109⟩]
theorem checked12828 : checkPrefixCuts (2^48) 1685323777 9 Manual.Count131072.C012828.packed 128 cuts12828 = true := by
 decide +kernel
def pointBounds12828 : List (Nat × Nat × Nat) := [(1685346304,94208708306365,94209084903261),(1685399552,94209119486054,94209496083250),(1685452800,94209537165964,94209913763465)]
theorem point_links_checked12828 : (cuts12828.take 3).map (fun c => (1685323777-1+2*2^9*c.k,94208525592827+c.lower,94208902189591+c.upper)) = pointBounds12828 := by
 decide +kernel
def cuts12829 : List PrefixCut := [⟨50,392783639,392783927⟩,
⟨102,809435162,809435756⟩,
⟨128,1015668649,1015669392⟩]
theorem checked12829 : checkPrefixCuts (2^48) 1685454849 9 Manual.Count131072.C012829.packed 128 cuts12829 = true := by
 decide +kernel
def pointBounds12829 : List (Nat × Nat × Nat) := [(1685506048,94209945313827,94210321911627),(1685559296,94210361965350,94210738563456)]
theorem point_links_checked12829 : (cuts12829.take 2).map (fun c => (1685454849-1+2*2^9*c.k,94209552530188+c.lower,94209929127700+c.upper)) = pointBounds12829 := by
 decide +kernel
def cuts12830 : List PrefixCut := [⟨26,207566102,207566255⟩,
⟨78,618012900,618013355⟩,
⟨128,1014420773,1014421517⟩]
theorem checked12830 : checkPrefixCuts (2^48) 1685585921 9 Manual.Count131072.C012830.packed 128 cuts12830 = true := by
 decide +kernel
def pointBounds12830 : List (Nat × Nat × Nat) := [(1685612544,94210775764939,94211152363347),(1685665792,94211186211737,94211562810447)]
theorem point_links_checked12830 : (cuts12830.take 2).map (fun c => (1685585921-1+2*2^9*c.k,94210568198837+c.lower,94210944797092+c.upper)) = pointBounds12830 := by
 decide +kernel
def cuts12831 : List PrefixCut := [⟨2,16029720,16029732⟩,
⟨54,431292772,431293089⟩,
⟨106,852386662,852387291⟩,
⟨128,1031706496,1031707258⟩]
theorem checked12831 : checkPrefixCuts (2^48) 1685716993 9 Manual.Count131072.C012831.packed 128 cuts12831 = true := by
 decide +kernel
def pointBounds12831 : List (Nat × Nat × Nat) := [(1685719040,94211598649330,94211975248341),(1685772288,94212013912382,94212390511698),(1685825536,94212435006272,94212811605900)]
theorem point_links_checked12831 : (cuts12831.take 3).map (fun c => (1685716993-1+2*2^9*c.k,94211582619610+c.lower,94211959218609+c.upper)) = pointBounds12831 := by
 decide +kernel
def cuts12832 : List PrefixCut := [⟨30,231910032,231910205⟩,
⟨82,645965182,645965655⟩,
⟨128,1026450482,1026451231⟩]
theorem checked12832 : checkPrefixCuts (2^48) 1685848065 9 Manual.Count131072.C012832.packed 128 cuts12832 = true := by
 decide +kernel
def pointBounds12832 : List (Nat × Nat × Nat) := [(1685878784,94212846236138,94213222836072),(1685932032,94213260291288,94213636891522)]
theorem point_links_checked12832 : (cuts12832.take 2).map (fun c => (1685848065-1+2*2^9*c.k,94212614326106+c.lower,94212990925867+c.upper)) = pointBounds12832 := by
 decide +kernel
def cuts12833 : List PrefixCut := [⟨6,44909572,44909605⟩,
⟨58,463780083,463780423⟩,
⟨110,877962853,877963496⟩,
⟨128,1027205726,1027206478⟩]
theorem checked12833 : checkPrefixCuts (2^48) 1685979137 9 Manual.Count131072.C012833.packed 128 cuts12833 = true := by
 decide +kernel
def pointBounds12833 : List (Nat × Nat × Nat) := [(1685985280,94213685686160,94214062286703),(1686038528,94214104556671,94214481157521),(1686091776,94214518739441,94214895340594)]
theorem point_links_checked12833 : (cuts12833.take 3).map (fun c => (1685979137-1+2*2^9*c.k,94213640776588+c.lower,94214017377098+c.upper)) = pointBounds12833 := by
 decide +kernel
def cuts12834 : List PrefixCut := [⟨34,278615648,278615851⟩,
⟨86,698948684,698949192⟩,
⟨128,1035639531,1035640286⟩]
theorem checked12834 : checkPrefixCuts (2^48) 1686110209 9 Manual.Count131072.C012834.packed 128 cuts12834 = true := by
 decide +kernel
def pointBounds12834 : List (Nat × Nat × Nat) := [(1686145024,94214946597962,94215323199427),(1686198272,94215366930998,94215743532768)]
theorem point_links_checked12834 : (cuts12834.take 2).map (fun c => (1686110209-1+2*2^9*c.k,94214667982314+c.lower,94215044583576+c.upper)) = pointBounds12834 := by
 decide +kernel
def cuts12835 : List PrefixCut := [⟨10,82293498,82293559⟩,
⟨62,490080931,490081291⟩,
⟨114,911876447,911877116⟩,
⟨128,1024041416,1024042167⟩]
theorem checked12835 : checkPrefixCuts (2^48) 1686241281 9 Manual.Count131072.C012835.packed 128 cuts12835 = true := by
 decide +kernel
def pointBounds12835 : List (Nat × Nat × Nat) := [(1686251520,94215785915343,94216162517421),(1686304768,94216193702776,94216570305153),(1686358016,94216615498292,94216992100978)]
theorem point_links_checked12835 : (cuts12835.take 3).map (fun c => (1686241281-1+2*2^9*c.k,94215703621845+c.lower,94216080223862+c.upper)) = pointBounds12835 := by
 decide +kernel
def cuts12836 : List PrefixCut := [⟨38,302606932,302607152⟩,
⟨90,722039153,722039683⟩,
⟨128,1024462682,1024463432⟩]
theorem checked12836 : checkPrefixCuts (2^48) 1686372353 9 Manual.Count131072.C012836.packed 128 cuts12836 = true := by
 decide +kernel
def pointBounds12836 : List (Nat × Nat × Nat) := [(1686411264,94217030270193,94217406873181),(1686464512,94217449702414,94217826305712)]
theorem point_links_checked12836 : (cuts12836.take 2).map (fun c => (1686372353-1+2*2^9*c.k,94216727663261+c.lower,94217104266029+c.upper)) = pointBounds12836 := by
 decide +kernel
def cuts12837 : List PrefixCut := [⟨14,110820131,110820211⟩,
⟨66,529725145,529725537⟩,
⟨118,951120312,951121015⟩,
⟨128,1032393817,1032394578⟩]
theorem checked12837 : checkPrefixCuts (2^48) 1686503425 9 Manual.Count131072.C012837.packed 128 cuts12837 = true := by
 decide +kernel
def pointBounds12837 : List (Nat × Nat × Nat) := [(1686517760,94217862946074,94218239549672),(1686571008,94218281851088,94218658454998),(1686624256,94218703246255,94219079850476)]
theorem point_links_checked12837 : (cuts12837.take 3).map (fun c => (1686503425-1+2*2^9*c.k,94217752125943+c.lower,94218128729461+c.upper)) = pointBounds12837 := by
 decide +kernel
def cuts12838 : List PrefixCut := [⟨42,348118781,348119039⟩,
⟨94,764814700,764815262⟩,
⟨128,1039156028,1039156787⟩]
theorem checked12838 : checkPrefixCuts (2^48) 1686634497 9 Manual.Count131072.C012838.packed 128 cuts12838 = true := by
 decide +kernel
def pointBounds12838 : List (Nat × Nat × Nat) := [(1686677504,94219132638541,94219509243078),(1686730752,94219549334460,94219925939301)]
theorem point_links_checked12838 : (cuts12838.take 2).map (fun c => (1686634497-1+2*2^9*c.k,94218784519760+c.lower,94219161124039+c.upper)) = pointBounds12838 := by
 decide +kernel
def cuts12839 : List PrefixCut := [⟨18,142007774,142007876⟩,
⟨70,564851484,564851898⟩,
⟨122,979505559,979506275⟩,
⟨128,1028395511,1028396261⟩]
theorem checked12839 : checkPrefixCuts (2^48) 1686765569 9 Manual.Count131072.C012839.packed 128 cuts12839 = true := by
 decide +kernel
def pointBounds12839 : List (Nat × Nat × Nat) := [(1686784000,94219965683562,94220342288702),(1686837248,94220388527272,94220765132724),(1686890496,94220803181347,94221179787101)]
theorem point_links_checked12839 : (cuts12839.take 3).map (fun c => (1686765569-1+2*2^9*c.k,94219823675788+c.lower,94220200280826+c.upper)) = pointBounds12839 := by
 decide +kernel
def cuts12840 : List PrefixCut := [⟨46,370423144,370423412⟩,
⟨98,799233518,799234095⟩,
⟨128,1038326893,1038327645⟩]
theorem checked12840 : checkPrefixCuts (2^48) 1686896641 9 Manual.Count131072.C012840.packed 128 cuts12840 = true := by
 decide +kernel
def pointBounds12840 : List (Nat × Nat × Nat) := [(1686943744,94221222494443,94221599100499),(1686996992,94221651304817,94222027911182)]
theorem point_links_checked12840 : (cuts12840.take 2).map (fun c => (1686896641-1+2*2^9*c.k,94220852071299+c.lower,94221228677087+c.upper)) = pointBounds12840 := by
 decide +kernel
def cuts12841 : List PrefixCut := [⟨22,176355743,176355871⟩,
⟨74,600467455,600467891⟩,
⟨126,1008382613,1008383350⟩,
⟨128,1023731319,1023732067⟩]
theorem checked12841 : checkPrefixCuts (2^48) 1687027713 9 Manual.Count131072.C012841.packed 128 cuts12841 = true := by
 decide +kernel
def pointBounds12841 : List (Nat × Nat × Nat) := [(1687050240,94222066753935,94222443360603),(1687103488,94222490865647,94222867472623),(1687156736,94222898780805,94223275388082)]
theorem point_links_checked12841 : (cuts12841.take 3).map (fun c => (1687027713-1+2*2^9*c.k,94221890398192+c.lower,94222267004732+c.upper)) = pointBounds12841 := by
 decide +kernel
def cuts12842 : List PrefixCut := [⟨50,393387794,393388083⟩,
⟨102,820962734,820963334⟩,
⟨128,1027822038,1027822790⟩]
theorem checked12842 : checkPrefixCuts (2^48) 1687158785 9 Manual.Count131072.C012842.packed 128 cuts12842 = true := by
 decide +kernel
def pointBounds12842 : List (Nat × Nat × Nat) := [(1687209984,94223307517305,94223684124882),(1687263232,94223735092245,94224111700133)]
theorem point_links_checked12842 : (cuts12842.take 2).map (fun c => (1687158785-1+2*2^9*c.k,94222914129511+c.lower,94223290736799+c.upper)) = pointBounds12842 := by
 decide +kernel
def cuts12843 : List PrefixCut := [⟨26,215030159,215030314⟩,
⟨78,643912612,643913075⟩,
⟨128,1050429277,1050430035⟩]
theorem checked12843 : checkPrefixCuts (2^48) 1687289857 9 Manual.Count131072.C012843.packed 128 cuts12843 = true := by
 decide +kernel
def pointBounds12843 : List (Nat × Nat × Nat) := [(1687316480,94224156981708,94224533589903),(1687369728,94224585864161,94224962472664)]
theorem point_links_checked12843 : (cuts12843.take 2).map (fun c => (1687289857-1+2*2^9*c.k,94223941951549+c.lower,94224318559589+c.upper)) = pointBounds12843 := by
 decide +kernel
def cuts12844 : List PrefixCut := [⟨2,16513957,16513968⟩,
⟨54,435861431,435861743⟩,
⟨106,848857402,848858019⟩,
⟨128,1025327445,1025328192⟩]
theorem checked12844 : checkPrefixCuts (2^48) 1687420929 9 Manual.Count131072.C012844.packed 128 cuts12844 = true := by
 decide +kernel
def pointBounds12844 : List (Nat × Nat × Nat) := [(1687422976,94225008894783,94225385503592),(1687476224,94225428242257,94225804851367),(1687529472,94225841238228,94226217847643)]
theorem point_links_checked12844 : (cuts12844.take 3).map (fun c => (1687420929-1+2*2^9*c.k,94224992380826+c.lower,94225368989624+c.upper)) = pointBounds12844 := by
 decide +kernel
def cuts12845 : List PrefixCut := [⟨30,239348374,239348549⟩,
⟨82,655153633,655154111⟩,
⟨128,1025414533,1025415280⟩]
theorem checked12845 : checkPrefixCuts (2^48) 1687552001 9 Manual.Count131072.C012845.packed 128 cuts12845 = true := by
 decide +kernel
def pointBounds12845 : List (Nat × Nat × Nat) := [(1687582720,94226257056645,94226633666365),(1687635968,94226672861904,94227049471927)]
theorem point_links_checked12845 : (cuts12845.take 2).map (fun c => (1687552001-1+2*2^9*c.k,94226017708271+c.lower,94226394317816+c.upper)) = pointBounds12845 := by
 decide +kernel
def cuts12846 : List PrefixCut := [⟨6,47699517,47699552⟩,
⟨58,465813440,465813781⟩,
⟨110,882580046,882580688⟩,
⟨128,1031839013,1031839764⟩]
theorem checked12846 : checkPrefixCuts (2^48) 1687683073 9 Manual.Count131072.C012846.packed 128 cuts12846 = true := by
 decide +kernel
def pointBounds12846 : List (Nat × Nat × Nat) := [(1687689216,94227090822321,94227467432648),(1687742464,94227508936244,94227885546877),(1687795712,94227925702850,94228302313784)]
theorem point_links_checked12846 : (cuts12846.take 3).map (fun c => (1687683073-1+2*2^9*c.k,94227043122804+c.lower,94227419733096+c.upper)) = pointBounds12846 := by
 decide +kernel
def cuts12847 : List PrefixCut := [⟨34,277834088,277834287⟩,
⟨86,699743972,699744477⟩,
⟨128,1037095456,1037096207⟩]
theorem checked12847 : checkPrefixCuts (2^48) 1687814145 9 Manual.Count131072.C012847.packed 128 cuts12847 = true := by
 decide +kernel
def pointBounds12847 : List (Nat × Nat × Nat) := [(1687848960,94228352795905,94228729407147),(1687902208,94228774705789,94229151317337)]
theorem point_links_checked12847 : (cuts12847.take 2).map (fun c => (1687814145-1+2*2^9*c.k,94228074961817+c.lower,94228451572860+c.upper)) = pointBounds12847 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000088
