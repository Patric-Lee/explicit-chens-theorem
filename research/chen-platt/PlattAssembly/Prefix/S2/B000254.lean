import PlattAssemblyKernel
import PlattCertificates.Count131072.C018128
import PlattCertificates.Count131072.C018129
import PlattCertificates.Count131072.C018130
import PlattCertificates.Count131072.C018131
import PlattCertificates.Count131072.C018132
import PlattCertificates.Count131072.C018133
import PlattCertificates.Count131072.C018134
import PlattCertificates.Count131072.C018135
import PlattCertificates.Count131072.C018136
import PlattCertificates.Count131072.C018137
import PlattCertificates.Count131072.C018138
import PlattCertificates.Count131072.C018139
import PlattCertificates.Count131072.C018140
import PlattCertificates.Count131072.C018141
import PlattCertificates.Count131072.C018142
import PlattCertificates.Count131072.C018143
import PlattCertificates.Count131072.C018144
import PlattCertificates.Count131072.C018145
import PlattCertificates.Count131072.C018146
import PlattCertificates.Count131072.C018147
import PlattCertificates.Count131072.C018148
import PlattCertificates.Count131072.C018149
import PlattCertificates.Count131072.C018150
import PlattCertificates.Count131072.C018151
import PlattCertificates.Count131072.C018152
import PlattCertificates.Count131072.C018153
import PlattCertificates.Count131072.C018154
import PlattCertificates.Count131072.C018155
import PlattCertificates.Count131072.C018156
import PlattCertificates.Count131072.C018157
import PlattCertificates.Count131072.C018158
import PlattCertificates.Count131072.C018159
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000254
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18128 : List PrefixCut := [⟨73,419366402,419366658⟩,
⟨128,716320755,716321192⟩]
theorem checked18128 : checkPrefixCuts (2^48) 2380005377 9 Manual.Count131072.C018128.packed 128 cuts18128 = true := by
 decide +kernel
def pointBounds18128 : List (Nat × Nat × Nat) := [(2380080128,98744906930821,98745286537791)]
theorem point_links_checked18128 : (cuts18128.take 1).map (fun c => (2380005377-1+2*2^9*c.k,98744487564419+c.lower,98744867171133+c.upper)) = pointBounds18128 := by
 decide +kernel
def cuts18129 : List PrefixCut := [⟨18,103595342,103595408⟩,
⟨91,505196894,505197204⟩,
⟨128,712733398,712733834⟩]
theorem checked18129 : checkPrefixCuts (2^48) 2380136449 9 Manual.Count131072.C018129.packed 128 cuts18129 = true := by
 decide +kernel
def pointBounds18129 : List (Nat × Nat × Nat) := [(2380154880,98745307480516,98745687087733),(2380229632,98745709082068,98746088689529)]
theorem point_links_checked18129 : (cuts18129.take 2).map (fun c => (2380136449-1+2*2^9*c.k,98745203885174+c.lower,98745583492325+c.upper)) = pointBounds18129 := by
 decide +kernel
def cuts18130 : List PrefixCut := [⟨36,197008779,197008905⟩,
⟨109,602960160,602960525⟩,
⟨128,712339039,712339469⟩]
theorem checked18130 : checkPrefixCuts (2^48) 2380267521 9 Manual.Count131072.C018130.packed 128 cuts18130 = true := by
 decide +kernel
def pointBounds18130 : List (Nat × Nat × Nat) := [(2380304384,98746113627351,98746493235064),(2380379136,98746519578732,98746899186684)]
theorem point_links_checked18130 : (cuts18130.take 2).map (fun c => (2380267521-1+2*2^9*c.k,98745916618572+c.lower,98746296226159+c.upper)) = pointBounds18130 := by
 decide +kernel
def cuts18131 : List PrefixCut := [⟨54,302472230,302472417⟩,
⟨127,717029886,717030326⟩,
⟨128,722468948,722469391⟩]
theorem checked18131 : checkPrefixCuts (2^48) 2380398593 9 Manual.Count131072.C018131.packed 128 cuts18131 = true := by
 decide +kernel
def pointBounds18131 : List (Nat × Nat × Nat) := [(2380453888,98746931429841,98747311038045),(2380528640,98747345987497,98747725595954)]
theorem point_links_checked18131 : (cuts18131.take 2).map (fun c => (2380398593-1+2*2^9*c.k,98746628957611+c.lower,98747008565628+c.upper)) = pointBounds18131 := by
 decide +kernel
def cuts18132 : List PrefixCut := [⟨72,402129541,402129782⟩,
⟨128,708359132,708359565⟩]
theorem checked18132 : checkPrefixCuts (2^48) 2380529665 9 Manual.Count131072.C018132.packed 128 cuts18132 = true := by
 decide +kernel
def pointBounds18132 : List (Nat × Nat × Nat) := [(2380603392,98747753556100,98748133164801)]
theorem point_links_checked18132 : (cuts18132.take 1).map (fun c => (2380529665-1+2*2^9*c.k,98747351426559+c.lower,98747731035019+c.upper)) = pointBounds18132 := by
 decide +kernel
def cuts18133 : List PrefixCut := [⟨17,92222131,92222190⟩,
⟨90,508277746,508278057⟩,
⟨128,722271131,722271573⟩]
theorem checked18133 : checkPrefixCuts (2^48) 2380660737 9 Manual.Count131072.C018133.packed 128 cuts18133 = true := by
 decide +kernel
def pointBounds18133 : List (Nat × Nat × Nat) := [(2380678144,98748152007822,98748531616774),(2380752896,98748568063437,98748947672641)]
theorem point_links_checked18133 : (cuts18133.take 2).map (fun c => (2380660737-1+2*2^9*c.k,98748059785691+c.lower,98748439394584+c.upper)) = pointBounds18133 := by
 decide +kernel
def cuts18134 : List PrefixCut := [⟨35,202640297,202640421⟩,
⟨108,609684778,609685148⟩,
⟨128,719985373,719985811⟩]
theorem checked18134 : checkPrefixCuts (2^48) 2380791809 9 Manual.Count131072.C018134.packed 128 cuts18134 = true := by
 decide +kernel
def pointBounds18134 : List (Nat × Nat × Nat) := [(2380827648,98748984697119,98749364306578),(2380902400,98749391741600,98749771351305)]
theorem point_links_checked18134 : (cuts18134.take 2).map (fun c => (2380791809-1+2*2^9*c.k,98748782056822+c.lower,98749161666157+c.upper)) = pointBounds18134 := by
 decide +kernel
def cuts18135 : List PrefixCut := [⟨53,302287456,302287642⟩,
⟨126,708124265,708124696⟩,
⟨128,719236424,719236862⟩]
theorem checked18135 : checkPrefixCuts (2^48) 2380922881 9 Manual.Count131072.C018135.packed 128 cuts18135 = true := by
 decide +kernel
def pointBounds18135 : List (Nat × Nat × Nat) := [(2380977152,98749804329651,98750183939610),(2381051904,98750210166460,98750589776664)]
theorem point_links_checked18135 : (cuts18135.take 2).map (fun c => (2380922881-1+2*2^9*c.k,98749502042195+c.lower,98749881651968+c.upper)) = pointBounds18135 := by
 decide +kernel
def cuts18136 : List PrefixCut := [⟨71,394475442,394475679⟩,
⟨128,710921888,710922316⟩]
theorem checked18136 : checkPrefixCuts (2^48) 2381053953 9 Manual.Count131072.C018136.packed 128 cuts18136 = true := by
 decide +kernel
def pointBounds18136 : List (Nat × Nat × Nat) := [(2381126656,98750615754061,98750995364509)]
theorem point_links_checked18136 : (cuts18136.take 1).map (fun c => (2381053953-1+2*2^9*c.k,98750221278619+c.lower,98750600888830+c.upper)) = pointBounds18136 := by
 decide +kernel
def cuts18137 : List PrefixCut := [⟨16,92556476,92556532⟩,
⟨89,505092703,505093008⟩,
⟨128,724239955,724240393⟩]
theorem checked18137 : checkPrefixCuts (2^48) 2381185025 9 Manual.Count131072.C018137.packed 128 cuts18137 = true := by
 decide +kernel
def pointBounds18137 : List (Nat × Nat × Nat) := [(2381201408,98751024756983,98751404367678),(2381276160,98751437293210,98751816904154)]
theorem point_links_checked18137 : (cuts18137.take 2).map (fun c => (2381185025-1+2*2^9*c.k,98750932200507+c.lower,98751311811146+c.upper)) = pointBounds18137 := by
 decide +kernel
def cuts18138 : List PrefixCut := [⟨34,191366665,191366779⟩,
⟨107,601394845,601395210⟩,
⟨128,716753573,716754008⟩]
theorem checked18138 : checkPrefixCuts (2^48) 2381316097 9 Manual.Count131072.C018138.packed 128 cuts18138 = true := by
 decide +kernel
def pointBounds18138 : List (Nat × Nat × Nat) := [(2381350912,98751847807127,98752227418318),(2381425664,98752257835307,98752637446749)]
theorem point_links_checked18138 : (cuts18138.take 2).map (fun c => (2381316097-1+2*2^9*c.k,98751656440462+c.lower,98752036051539+c.upper)) = pointBounds18138 := by
 decide +kernel
def cuts18139 : List PrefixCut := [⟨52,289810623,289810801⟩,
⟨125,694849053,694849479⟩,
⟨128,710331742,710332179⟩]
theorem checked18139 : checkPrefixCuts (2^48) 2381447169 9 Manual.Count131072.C018139.packed 128 cuts18139 = true := by
 decide +kernel
def pointBounds18139 : List (Nat × Nat × Nat) := [(2381500416,98752663004658,98753042616348),(2381575168,98753068043088,98753447655026)]
theorem point_links_checked18139 : (cuts18139.take 2).map (fun c => (2381447169-1+2*2^9*c.k,98752373194035+c.lower,98752752805547+c.upper)) = pointBounds18139 := by
 decide +kernel
def cuts18140 : List PrefixCut := [⟨70,390606755,390606989⟩,
⟨128,711120002,711120432⟩]
theorem checked18140 : checkPrefixCuts (2^48) 2381578241 9 Manual.Count131072.C018140.packed 128 cuts18140 = true := by
 decide +kernel
def pointBounds18140 : List (Nat × Nat × Nat) := [(2381649920,98753474132532,98753853744715)]
theorem point_links_checked18140 : (cuts18140.take 1).map (fun c => (2381578241-1+2*2^9*c.k,98753083525777+c.lower,98753463137726+c.upper)) = pointBounds18140 := by
 decide +kernel
def cuts18141 : List PrefixCut := [⟨15,86863397,86863449⟩,
⟨88,501554494,501554797⟩,
⟨128,723253428,723253868⟩]
theorem checked18141 : checkPrefixCuts (2^48) 2381709313 9 Manual.Count131072.C018141.packed 128 cuts18141 = true := by
 decide +kernel
def pointBounds18141 : List (Nat × Nat × Nat) := [(2381724672,98753881509176,98754261121607),(2381799424,98754296200273,98754675812955)]
theorem point_links_checked18141 : (cuts18141.take 2).map (fun c => (2381709313-1+2*2^9*c.k,98753794645779+c.lower,98754174258158+c.upper)) = pointBounds18141 := by
 decide +kernel
def cuts18142 : List PrefixCut := [⟨33,184588625,184588738⟩,
⟨106,593463245,593463610⟩,
⟨128,716241280,716241717⟩]
theorem checked18142 : checkPrefixCuts (2^48) 2381840385 9 Manual.Count131072.C018142.packed 128 cuts18142 = true := by
 decide +kernel
def pointBounds18142 : List (Nat × Nat × Nat) := [(2381874176,98754702487832,98755082100764),(2381948928,98755111362452,98755490975636)]
theorem point_links_checked18142 : (cuts18142.take 2).map (fun c => (2381840385-1+2*2^9*c.k,98754517899207+c.lower,98754897512026+c.upper)) = pointBounds18142 := by
 decide +kernel
def cuts18143 : List PrefixCut := [⟨51,283720381,283720553⟩,
⟨124,693750959,693751376⟩,
⟨128,718210591,718211023⟩]
theorem checked18143 : checkPrefixCuts (2^48) 2381971457 9 Manual.Count131072.C018143.packed 128 cuts18143 = true := by
 decide +kernel
def pointBounds18143 : List (Nat × Nat × Nat) := [(2382023680,98755517860868,98755897474296),(2382098432,98755927891446,98756307505119)]
theorem point_links_checked18143 : (cuts18143.take 2).map (fun c => (2381971457-1+2*2^9*c.k,98755234140487+c.lower,98755613753743+c.upper)) = pointBounds18143 := by
 decide +kernel
def cuts18144 : List PrefixCut := [⟨69,385439938,385440171⟩,
⟨128,718998153,718998596⟩]
theorem checked18144 : checkPrefixCuts (2^48) 2382102529 9 Manual.Count131072.C018144.packed 128 cuts18144 = true := by
 decide +kernel
def pointBounds18144 : List (Nat × Nat × Nat) := [(2382173184,98756337791016,98756717404937)]
theorem point_links_checked18144 : (cuts18144.take 1).map (fun c => (2382102529-1+2*2^9*c.k,98755952351078+c.lower,98756331964766+c.upper)) = pointBounds18144 := by
 decide +kernel
def cuts18145 : List PrefixCut := [⟨14,79991287,79991338⟩,
⟨87,486911245,486911550⟩,
⟨128,717422698,717423146⟩]
theorem checked18145 : checkPrefixCuts (2^48) 2382233601 9 Manual.Count131072.C018145.packed 128 cuts18145 = true := by
 decide +kernel
def pointBounds18145 : List (Nat × Nat × Nat) := [(2382247936,98756751340518,98757130954700),(2382322688,98757158260476,98757537874912)]
theorem point_links_checked18145 : (cuts18145.take 2).map (fun c => (2382233601-1+2*2^9*c.k,98756671349231+c.lower,98757050963362+c.upper)) = pointBounds18145 := by
 decide +kernel
def cuts18146 : List PrefixCut := [⟨32,177222847,177222954⟩,
⟨105,591442317,591442674⟩,
⟨128,715729218,715729649⟩]
theorem checked18146 : checkPrefixCuts (2^48) 2382364673 9 Manual.Count131072.C018146.packed 128 cuts18146 = true := by
 decide +kernel
def pointBounds18146 : List (Nat × Nat × Nat) := [(2382397440,98757565994776,98757945609462),(2382472192,98757980214246,98758359829182)]
theorem point_links_checked18146 : (cuts18146.take 2).map (fun c => (2382364673-1+2*2^9*c.k,98757388771929+c.lower,98757768386508+c.upper)) = pointBounds18146 := by
 decide +kernel
def cuts18147 : List PrefixCut := [⟨50,279404891,279405067⟩,
⟨123,694189080,694189504⟩,
⟨128,722896250,722896692⟩]
theorem checked18147 : checkPrefixCuts (2^48) 2382495745 9 Manual.Count131072.C018147.packed 128 cuts18147 = true := by
 decide +kernel
def pointBounds18147 : List (Nat × Nat × Nat) := [(2382546944,98758383906038,98758763521224),(2382621696,98758798690227,98759178305661)]
theorem point_links_checked18147 : (cuts18147.take 2).map (fun c => (2382495745-1+2*2^9*c.k,98758104501147+c.lower,98758484116157+c.upper)) = pointBounds18147 := by
 decide +kernel
def cuts18148 : List PrefixCut := [⟨68,385591467,385591709⟩,
⟨128,716713784,716714232⟩]
theorem checked18148 : checkPrefixCuts (2^48) 2382626817 9 Manual.Count131072.C018148.packed 128 cuts18148 = true := by
 decide +kernel
def pointBounds18148 : List (Nat × Nat × Nat) := [(2382696448,98759212988864,98759592604558)]
theorem point_links_checked18148 : (cuts18148.take 1).map (fun c => (2382626817-1+2*2^9*c.k,98758827397397+c.lower,98759207012849+c.upper)) = pointBounds18148 := by
 decide +kernel
def cuts18149 : List PrefixCut := [⟨13,73004060,73004104⟩,
⟨86,484796072,484796362⟩,
⟨128,717146840,717147270⟩]
theorem checked18149 : checkPrefixCuts (2^48) 2382757889 9 Manual.Count131072.C018149.packed 128 cuts18149 = true := by
 decide +kernel
def pointBounds18149 : List (Nat × Nat × Nat) := [(2382771200,98759617115241,98759996731185),(2382845952,98760028907253,98760408523443)]
theorem point_links_checked18149 : (cuts18149.take 2).map (fun c => (2382757889-1+2*2^9*c.k,98759544111181+c.lower,98759923727081+c.upper)) = pointBounds18149 := by
 decide +kernel
def cuts18150 : List PrefixCut := [⟨31,171395880,171395983⟩,
⟨104,578319189,578319538⟩,
⟨128,715926076,715926507⟩]
theorem checked18150 : checkPrefixCuts (2^48) 2382888961 9 Manual.Count131072.C018150.packed 128 cuts18150 = true := by
 decide +kernel
def pointBounds18150 : List (Nat × Nat × Nat) := [(2382920704,98760432653901,98760812270334),(2382995456,98760839577210,98761219193889)]
theorem point_links_checked18150 : (cuts18150.take 2).map (fun c => (2382888961-1+2*2^9*c.k,98760261258021+c.lower,98760640874351+c.upper)) = pointBounds18150 := by
 decide +kernel
def cuts18151 : List PrefixCut := [⟨49,272374627,272374797⟩,
⟨122,685059893,685060309⟩,
⟨128,718721397,718721832⟩]
theorem checked18151 : checkPrefixCuts (2^48) 2383020033 9 Manual.Count131072.C018151.packed 128 cuts18151 = true := by
 decide +kernel
def pointBounds18151 : List (Nat × Nat × Nat) := [(2383070208,98761249558724,98761629175655),(2383144960,98761662243990,98762041861167)]
theorem point_links_checked18151 : (cuts18151.take 2).map (fun c => (2383020033-1+2*2^9*c.k,98760977184097+c.lower,98761356800858+c.upper)) = pointBounds18151 := by
 decide +kernel
def cuts18152 : List PrefixCut := [⟨67,372042367,372042591⟩,
⟨128,714548133,714548562⟩]
theorem checked18152 : checkPrefixCuts (2^48) 2383151105 9 Manual.Count131072.C018152.packed 128 cuts18152 = true := by
 decide +kernel
def pointBounds18152 : List (Nat × Nat × Nat) := [(2383219712,98762067947861,98762447565281)]
theorem point_links_checked18152 : (cuts18152.take 1).map (fun c => (2383151105-1+2*2^9*c.k,98761695905494+c.lower,98762075522690+c.upper)) = pointBounds18152 := by
 decide +kernel
def cuts18153 : List PrefixCut := [⟨12,67673355,67673397⟩,
⟨85,481028372,481028667⟩,
⟨128,721831126,721831571⟩]
theorem checked18153 : checkPrefixCuts (2^48) 2383282177 9 Manual.Count131072.C018153.packed 128 cuts18153 = true := by
 decide +kernel
def pointBounds18153 : List (Nat × Nat × Nat) := [(2383294464,98762478126982,98762857744649),(2383369216,98762891481999,98763271099919)]
theorem point_links_checked18153 : (cuts18153.take 2).map (fun c => (2383282177-1+2*2^9*c.k,98762410453627+c.lower,98762790071252+c.upper)) = pointBounds18153 := by
 decide +kernel
def cuts18154 : List PrefixCut := [⟨30,173011583,173011688⟩,
⟨103,580554026,580554380⟩,
⟨128,720138211,720138650⟩]
theorem checked18154 : checkPrefixCuts (2^48) 2383413249 9 Manual.Count131072.C018154.packed 128 cuts18154 = true := by
 decide +kernel
def pointBounds18154 : List (Nat × Nat × Nat) := [(2383443968,98763305296336,98763684914511),(2383518720,98763712838779,98764092457203)]
theorem point_links_checked18154 : (cuts18154.take 2).map (fun c => (2383413249-1+2*2^9*c.k,98763132284753+c.lower,98763511902823+c.upper)) = pointBounds18154 := by
 decide +kernel
def cuts18155 : List PrefixCut := [⟨48,267118886,267119051⟩,
⟨121,681839077,681839494⟩,
⟨128,721751668,721752109⟩]
theorem checked18155 : checkPrefixCuts (2^48) 2383544321 9 Manual.Count131072.C018155.packed 128 cuts18155 = true := by
 decide +kernel
def pointBounds18155 : List (Nat × Nat × Nat) := [(2383593472,98764119541850,98764499160524),(2383668224,98764534262041,98764913880967)]
theorem point_links_checked18155 : (cuts18155.take 2).map (fun c => (2383544321-1+2*2^9*c.k,98763852422964+c.lower,98764232041473+c.upper)) = pointBounds18155 := by
 decide +kernel
def cuts18156 : List PrefixCut := [⟨66,371842541,371842765⟩,
⟨128,724191723,724192166⟩]
theorem checked18156 : checkPrefixCuts (2^48) 2383675393 9 Manual.Count131072.C018156.packed 128 cuts18156 = true := by
 decide +kernel
def pointBounds18156 : List (Nat × Nat × Nat) := [(2383742976,98764946017173,98765325636347)]
theorem point_links_checked18156 : (cuts18156.take 1).map (fun c => (2383675393-1+2*2^9*c.k,98764574174632+c.lower,98764953793582+c.upper)) = pointBounds18156 := by
 decide +kernel
def cuts18157 : List PrefixCut := [⟨11,61754603,61754641⟩,
⟨84,473247720,473248007⟩,
⟨128,719665064,719665503⟩]
theorem checked18157 : checkPrefixCuts (2^48) 2383806465 9 Manual.Count131072.C018157.packed 128 cuts18157 = true := by
 decide +kernel
def pointBounds18157 : List (Nat × Nat × Nat) := [(2383817728,98765360120958,98765739740389),(2383892480,98765771614075,98766151233755)]
theorem point_links_checked18157 : (cuts18157.take 2).map (fun c => (2383806465-1+2*2^9*c.k,98765298366355+c.lower,98765677985748+c.upper)) = pointBounds18157 := by
 decide +kernel
def cuts18158 : List PrefixCut := [⟨29,163882106,163882205⟩,
⟨102,575349427,575349778⟩,
⟨128,715729413,715729853⟩]
theorem checked18158 : checkPrefixCuts (2^48) 2383937537 9 Manual.Count131072.C018158.packed 128 cuts18158 = true := by
 decide +kernel
def pointBounds18158 : List (Nat × Nat × Nat) := [(2383967232,98766181913525,98766561533456),(2384041984,98766593380846,98766973001029)]
theorem point_links_checked18158 : (cuts18158.take 2).map (fun c => (2383937537-1+2*2^9*c.k,98766018031419+c.lower,98766397651251+c.upper)) = pointBounds18158 := by
 decide +kernel
def cuts18159 : List PrefixCut := [⟨47,263400211,263400369⟩,
⟨120,677084875,677085280⟩,
⟨128,724780567,724781000⟩]
theorem checked18159 : checkPrefixCuts (2^48) 2384068609 9 Manual.Count131072.C018159.packed 128 cuts18159 = true := by
 decide +kernel
def pointBounds18159 : List (Nat × Nat × Nat) := [(2384116736,98766997161043,98767376781473),(2384191488,98767410845707,98767790466384)]
theorem point_links_checked18159 : (cuts18159.take 2).map (fun c => (2384068609-1+2*2^9*c.k,98766733760832+c.lower,98767113381104+c.upper)) = pointBounds18159 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000254
