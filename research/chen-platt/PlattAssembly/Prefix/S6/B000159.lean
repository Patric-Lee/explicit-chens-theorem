import PlattAssemblyKernel
import PlattCertificates.Count131072.C055088
import PlattCertificates.Count131072.C055089
import PlattCertificates.Count131072.C055090
import PlattCertificates.Count131072.C055091
import PlattCertificates.Count131072.C055092
import PlattCertificates.Count131072.C055093
import PlattCertificates.Count131072.C055094
import PlattCertificates.Count131072.C055095
import PlattCertificates.Count131072.C055096
import PlattCertificates.Count131072.C055097
import PlattCertificates.Count131072.C055098
import PlattCertificates.Count131072.C055099
import PlattCertificates.Count131072.C055100
import PlattCertificates.Count131072.C055101
import PlattCertificates.Count131072.C055102
import PlattCertificates.Count131072.C055103
import PlattCertificates.Count131072.C055104
import PlattCertificates.Count131072.C055105
import PlattCertificates.Count131072.C055106
import PlattCertificates.Count131072.C055107
import PlattCertificates.Count131072.C055108
import PlattCertificates.Count131072.C055109
import PlattCertificates.Count131072.C055110
import PlattCertificates.Count131072.C055111
import PlattCertificates.Count131072.C055112
import PlattCertificates.Count131072.C055113
import PlattCertificates.Count131072.C055114
import PlattCertificates.Count131072.C055115
import PlattCertificates.Count131072.C055116
import PlattCertificates.Count131072.C055117
import PlattCertificates.Count131072.C055118
import PlattCertificates.Count131072.C055119
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000159
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts55088 : List PrefixCut := [⟨64,224611336,224611462⟩]
theorem checked55088 : checkPrefixCuts (2^48) 7224426497 10 Manual.Count131072.C055088.packed 64 cuts55088 = true := by
 decide +kernel
def cuts55089 : List PrefixCut := [⟨5,18506391,18506401⟩,
⟨64,227685149,227685278⟩]
theorem checked55089 : checkPrefixCuts (2^48) 7224557569 10 Manual.Count131072.C055089.packed 64 cuts55089 = true := by
 decide +kernel
def pointBounds55089 : List (Nat × Nat × Nat) := [(7224567808,112860560190502,112860947996508)]
theorem point_links_checked55089 : (cuts55089.take 1).map (fun c => (7224557569-1+2*2^10*c.k,112860541684111+c.lower,112860929490107+c.upper)) = pointBounds55089 := by
 decide +kernel
def cuts55090 : List PrefixCut := [⟨52,181513968,181514070⟩,
⟨64,223161676,223161802⟩]
theorem checked55090 : checkPrefixCuts (2^48) 7224688641 10 Manual.Count131072.C055090.packed 64 cuts55090 = true := by
 decide +kernel
def pointBounds55090 : List (Nat × Nat × Nat) := [(7224795136,112860950883228,112861338689455)]
theorem point_links_checked55090 : (cuts55090.take 1).map (fun c => (7224688641-1+2*2^10*c.k,112860769369260+c.lower,112861157175385+c.upper)) = pointBounds55090 := by
 decide +kernel
def cuts55091 : List PrefixCut := [⟨64,227326253,227326382⟩]
theorem checked55091 : checkPrefixCuts (2^48) 7224819713 10 Manual.Count131072.C055091.packed 64 cuts55091 = true := by
 decide +kernel
def cuts55092 : List PrefixCut := [⟨35,123186889,123186959⟩,
⟨64,224984619,224984748⟩]
theorem checked55092 : checkPrefixCuts (2^48) 7224950785 10 Manual.Count131072.C055092.packed 64 cuts55092 = true := by
 decide +kernel
def pointBounds55092 : List (Nat × Nat × Nat) := [(7225022464,112861343044078,112861730850528)]
theorem point_links_checked55092 : (cuts55092.take 1).map (fun c => (7224950785-1+2*2^10*c.k,112861219857189+c.lower,112861607663569+c.upper)) = pointBounds55092 := by
 decide +kernel
def cuts55093 : List PrefixCut := [⟨64,227279060,227279187⟩]
theorem checked55093 : checkPrefixCuts (2^48) 7225081857 10 Manual.Count131072.C055093.packed 64 cuts55093 = true := by
 decide +kernel
def cuts55094 : List PrefixCut := [⟨18,61630314,61630350⟩,
⟨64,225054350,225054479⟩]
theorem checked55094 : checkPrefixCuts (2^48) 7225212929 10 Manual.Count131072.C055094.packed 64 cuts55094 = true := by
 decide +kernel
def pointBounds55094 : List (Nat × Nat × Nat) := [(7225249792,112861733751182,112862121557854)]
theorem point_links_checked55094 : (cuts55094.take 1).map (fun c => (7225212929-1+2*2^10*c.k,112861672120868+c.lower,112862059927504+c.upper)) = pointBounds55094 := by
 decide +kernel
def cuts55095 : List PrefixCut := [⟨64,224621767,224621895⟩]
theorem checked55095 : checkPrefixCuts (2^48) 7225344001 10 Manual.Count131072.C055095.packed 64 cuts55095 = true := by
 decide +kernel
def cuts55096 : List PrefixCut := [⟨1,3739766,3739768⟩,
⟨64,226409660,226409788⟩]
theorem checked55096 : checkPrefixCuts (2^48) 7225475073 10 Manual.Count131072.C055096.packed 64 cuts55096 = true := by
 decide +kernel
def pointBounds55096 : List (Nat × Nat × Nat) := [(7225477120,112862125536751,112862513343646)]
theorem point_links_checked55096 : (cuts55096.take 1).map (fun c => (7225475073-1+2*2^10*c.k,112862121796985+c.lower,112862509603878+c.upper)) = pointBounds55096 := by
 decide +kernel
def cuts55097 : List PrefixCut := [⟨48,168791725,168791817⟩,
⟨64,224925267,224925392⟩]
theorem checked55097 : checkPrefixCuts (2^48) 7225606145 10 Manual.Count131072.C055097.packed 64 cuts55097 = true := by
 decide +kernel
def pointBounds55097 : List (Nat × Nat × Nat) := [(7225704448,112862516998370,112862904805483)]
theorem point_links_checked55097 : (cuts55097.take 1).map (fun c => (7225606145-1+2*2^10*c.k,112862348206645+c.lower,112862736013666+c.upper)) = pointBounds55097 := by
 decide +kernel
def cuts55098 : List PrefixCut := [⟨64,227141569,227141696⟩]
theorem checked55098 : checkPrefixCuts (2^48) 7225737217 10 Manual.Count131072.C055098.packed 64 cuts55098 = true := by
 decide +kernel
def cuts55099 : List PrefixCut := [⟨31,107706735,107706795⟩,
⟨64,223670584,223670710⟩]
theorem checked55099 : checkPrefixCuts (2^48) 7225868289 10 Manual.Count131072.C055099.packed 64 cuts55099 = true := by
 decide +kernel
def pointBounds55099 : List (Nat × Nat × Nat) := [(7225931776,112862907980216,112863295787549)]
theorem point_links_checked55099 : (cuts55099.take 1).map (fun c => (7225868289-1+2*2^10*c.k,112862800273481+c.lower,112863188080754+c.upper)) = pointBounds55099 := by
 decide +kernel
def cuts55100 : List PrefixCut := [⟨64,226704824,226704954⟩]
theorem checked55100 : checkPrefixCuts (2^48) 7225999361 10 Manual.Count131072.C055100.packed 64 cuts55100 = true := by
 decide +kernel
def cuts55101 : List PrefixCut := [⟨14,48456652,48456680⟩,
⟨64,224947873,224948002⟩]
theorem checked55101 : checkPrefixCuts (2^48) 7226130433 10 Manual.Count131072.C055101.packed 64 cuts55101 = true := by
 decide +kernel
def pointBounds55101 : List (Nat × Nat × Nat) := [(7226159104,112863299105541,112863686913098)]
theorem point_links_checked55101 : (cuts55101.take 1).map (fun c => (7226130433-1+2*2^10*c.k,112863250648889+c.lower,112863638456418+c.upper)) = pointBounds55101 := by
 decide +kernel
def cuts55102 : List PrefixCut := [⟨61,214037542,214037662⟩,
⟨64,224008991,224009117⟩]
theorem checked55102 : checkPrefixCuts (2^48) 7226261505 10 Manual.Count131072.C055102.packed 64 cuts55102 = true := by
 decide +kernel
def pointBounds55102 : List (Nat × Nat × Nat) := [(7226386432,112863689634304,112864077442082)]
theorem point_links_checked55102 : (cuts55102.take 1).map (fun c => (7226261505-1+2*2^10*c.k,112863475596762+c.lower,112863863404420+c.upper)) = pointBounds55102 := by
 decide +kernel
def cuts55103 : List PrefixCut := [⟨64,224783943,224784072⟩]
theorem checked55103 : checkPrefixCuts (2^48) 7226392577 10 Manual.Count131072.C055103.packed 64 cuts55103 = true := by
 decide +kernel
def cuts55104 : List PrefixCut := [⟨44,154787339,154787426⟩,
⟨64,223767172,223767299⟩]
theorem checked55104 : checkPrefixCuts (2^48) 7226523649 10 Manual.Count131072.C055104.packed 64 cuts55104 = true := by
 decide +kernel
def pointBounds55104 : List (Nat × Nat × Nat) := [(7226613760,112864079177035,112864466985035)]
theorem point_links_checked55104 : (cuts55104.take 1).map (fun c => (7226523649-1+2*2^10*c.k,112863924389696+c.lower,112864312197609+c.upper)) = pointBounds55104 := by
 decide +kernel
def cuts55105 : List PrefixCut := [⟨64,229644415,229644542⟩]
theorem checked55105 : checkPrefixCuts (2^48) 7226654721 10 Manual.Count131072.C055105.packed 64 cuts55105 = true := by
 decide +kernel
def cuts55106 : List PrefixCut := [⟨27,93126315,93126369⟩,
⟨64,223525340,223525464⟩]
theorem checked55106 : checkPrefixCuts (2^48) 7226785793 10 Manual.Count131072.C055106.packed 64 cuts55106 = true := by
 decide +kernel
def pointBounds55106 : List (Nat × Nat × Nat) := [(7226841088,112864470927598,112864858735819)]
theorem point_links_checked55106 : (cuts55106.take 1).map (fun c => (7226785793-1+2*2^10*c.k,112864377801283+c.lower,112864765609450+c.upper)) = pointBounds55106 := by
 decide +kernel
def cuts55107 : List PrefixCut := [⟨64,224027600,224027729⟩]
theorem checked55107 : checkPrefixCuts (2^48) 7226916865 10 Manual.Count131072.C055107.packed 64 cuts55107 = true := by
 decide +kernel
def cuts55108 : List PrefixCut := [⟨10,34818946,34818967⟩,
⟨64,222894078,222894206⟩]
theorem checked55108 : checkPrefixCuts (2^48) 7227047937 10 Manual.Count131072.C055108.packed 64 cuts55108 = true := by
 decide +kernel
def pointBounds55108 : List (Nat × Nat × Nat) := [(7227068416,112864860173169,112865247981610)]
theorem point_links_checked55108 : (cuts55108.take 1).map (fun c => (7227047937-1+2*2^10*c.k,112864825354223+c.lower,112865213162643+c.upper)) = pointBounds55108 := by
 decide +kernel
def cuts55109 : List PrefixCut := [⟨57,200262406,200262521⟩,
⟨64,224253172,224253302⟩]
theorem checked55109 : checkPrefixCuts (2^48) 7227179009 10 Manual.Count131072.C055109.packed 64 cuts55109 = true := by
 decide +kernel
def pointBounds55109 : List (Nat × Nat × Nat) := [(7227295744,112865248510707,112865636319370)]
theorem point_links_checked55109 : (cuts55109.take 1).map (fun c => (7227179009-1+2*2^10*c.k,112865048248301+c.lower,112865436056849+c.upper)) = pointBounds55109 := by
 decide +kernel
def cuts55110 : List PrefixCut := [⟨64,225612207,225612334⟩]
theorem checked55110 : checkPrefixCuts (2^48) 7227310081 10 Manual.Count131072.C055110.packed 64 cuts55110 = true := by
 decide +kernel
def cuts55111 : List PrefixCut := [⟨40,140981200,140981283⟩,
⟨64,225023927,225024055⟩]
theorem checked55111 : checkPrefixCuts (2^48) 7227441153 10 Manual.Count131072.C055111.packed 64 cuts55111 = true := by
 decide +kernel
def pointBounds55111 : List (Nat × Nat × Nat) := [(7227523072,112865639094880,112866026903768)]
theorem point_links_checked55111 : (cuts55111.take 1).map (fun c => (7227441153-1+2*2^10*c.k,112865498113680+c.lower,112865885922485+c.upper)) = pointBounds55111 := by
 decide +kernel
def cuts55112 : List PrefixCut := [⟨64,224864099,224864224⟩]
theorem checked55112 : checkPrefixCuts (2^48) 7227572225 10 Manual.Count131072.C055112.packed 64 cuts55112 = true := by
 decide +kernel
def cuts55113 : List PrefixCut := [⟨23,82443954,82444000⟩,
⟨64,227118725,227118853⟩]
theorem checked55113 : checkPrefixCuts (2^48) 7227703297 10 Manual.Count131072.C055113.packed 64 cuts55113 = true := by
 decide +kernel
def pointBounds55113 : List (Nat × Nat × Nat) := [(7227750400,112866030445660,112866418254764)]
theorem point_links_checked55113 : (cuts55113.take 1).map (fun c => (7227703297-1+2*2^10*c.k,112865948001706+c.lower,112866335810764+c.upper)) = pointBounds55113 := by
 decide +kernel
def cuts55114 : List PrefixCut := [⟨64,223220330,223220458⟩]
theorem checked55114 : checkPrefixCuts (2^48) 7227834369 10 Manual.Count131072.C055114.packed 64 cuts55114 = true := by
 decide +kernel
def cuts55115 : List PrefixCut := [⟨6,21418346,21418358⟩,
⟨64,225358095,225358225⟩]
theorem checked55115 : checkPrefixCuts (2^48) 7227965441 10 Manual.Count131072.C055115.packed 64 cuts55115 = true := by
 decide +kernel
def pointBounds55115 : List (Nat × Nat × Nat) := [(7227977728,112866419759107,112866807568433)]
theorem point_links_checked55115 : (cuts55115.take 1).map (fun c => (7227965441-1+2*2^10*c.k,112866398340761+c.lower,112866786150075+c.upper)) = pointBounds55115 := by
 decide +kernel
def cuts55116 : List PrefixCut := [⟨53,185283563,185283670⟩,
⟨64,222822809,222822937⟩]
theorem checked55116 : checkPrefixCuts (2^48) 7228096513 10 Manual.Count131072.C055116.packed 64 cuts55116 = true := by
 decide +kernel
def pointBounds55116 : List (Nat × Nat × Nat) := [(7228205056,112866808982419,112867196791970)]
theorem point_links_checked55116 : (cuts55116.take 1).map (fun c => (7228096513-1+2*2^10*c.k,112866623698856+c.lower,112867011508300+c.upper)) = pointBounds55116 := by
 decide +kernel
def cuts55117 : List PrefixCut := [⟨64,222039945,222040074⟩]
theorem checked55117 : checkPrefixCuts (2^48) 7228227585 10 Manual.Count131072.C055117.packed 64 cuts55117 = true := by
 decide +kernel
def cuts55118 : List PrefixCut := [⟨36,127139625,127139697⟩,
⟨64,226903413,226903542⟩]
theorem checked55118 : checkPrefixCuts (2^48) 7228358657 10 Manual.Count131072.C055118.packed 64 cuts55118 = true := by
 decide +kernel
def pointBounds55118 : List (Nat × Nat × Nat) := [(7228432384,112867195701235,112867583511008)]
theorem point_links_checked55118 : (cuts55118.take 1).map (fun c => (7228358657-1+2*2^10*c.k,112867068561610+c.lower,112867456371311+c.upper)) = pointBounds55118 := by
 decide +kernel
def cuts55119 : List PrefixCut := [⟨64,226393109,226393237⟩]
theorem checked55119 : checkPrefixCuts (2^48) 7228489729 10 Manual.Count131072.C055119.packed 64 cuts55119 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000159
