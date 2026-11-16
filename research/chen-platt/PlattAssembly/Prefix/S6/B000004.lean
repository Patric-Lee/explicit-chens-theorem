import PlattAssemblyKernel
import PlattCertificates.Count131072.C050128
import PlattCertificates.Count131072.C050129
import PlattCertificates.Count131072.C050130
import PlattCertificates.Count131072.C050131
import PlattCertificates.Count131072.C050132
import PlattCertificates.Count131072.C050133
import PlattCertificates.Count131072.C050134
import PlattCertificates.Count131072.C050135
import PlattCertificates.Count131072.C050136
import PlattCertificates.Count131072.C050137
import PlattCertificates.Count131072.C050138
import PlattCertificates.Count131072.C050139
import PlattCertificates.Count131072.C050140
import PlattCertificates.Count131072.C050141
import PlattCertificates.Count131072.C050142
import PlattCertificates.Count131072.C050143
import PlattCertificates.Count131072.C050144
import PlattCertificates.Count131072.C050145
import PlattCertificates.Count131072.C050146
import PlattCertificates.Count131072.C050147
import PlattCertificates.Count131072.C050148
import PlattCertificates.Count131072.C050149
import PlattCertificates.Count131072.C050150
import PlattCertificates.Count131072.C050151
import PlattCertificates.Count131072.C050152
import PlattCertificates.Count131072.C050153
import PlattCertificates.Count131072.C050154
import PlattCertificates.Count131072.C050155
import PlattCertificates.Count131072.C050156
import PlattCertificates.Count131072.C050157
import PlattCertificates.Count131072.C050158
import PlattCertificates.Count131072.C050159
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50128 : List PrefixCut := [⟨1,3810478,3810480⟩,
⟨64,251531885,251532029⟩]
theorem checked50128 : checkPrefixCuts (2^48) 6574309377 10 Manual.Count131072.C050128.packed 64 cuts50128 = true := by
 decide +kernel
def pointBounds50128 : List (Nat × Nat × Nat) := [(6574311424,111688671308695,111689058448872)]
theorem point_links_checked50128 : (cuts50128.take 1).map (fun c => (6574309377-1+2*2^10*c.k,111688667498217+c.lower,111689054638392+c.upper)) = pointBounds50128 := by
 decide +kernel
def cuts50129 : List PrefixCut := [⟨38,148861698,148861782⟩,
⟨64,249942805,249942944⟩]
theorem checked50129 : checkPrefixCuts (2^48) 6574440449 10 Manual.Count131072.C050129.packed 64 cuts50129 = true := by
 decide +kernel
def pointBounds50129 : List (Nat × Nat × Nat) := [(6574518272,111689067891800,111689455032203)]
theorem point_links_checked50129 : (cuts50129.take 1).map (fun c => (6574440449-1+2*2^10*c.k,111688919030102+c.lower,111689306170421+c.upper)) = pointBounds50129 := by
 decide +kernel
def cuts50130 : List PrefixCut := [⟨64,248696268,248696410⟩]
theorem checked50130 : checkPrefixCuts (2^48) 6574571521 10 Manual.Count131072.C050130.packed 64 cuts50130 = true := by
 decide +kernel
def cuts50131 : List PrefixCut := [⟨11,41270511,41270535⟩,
⟨64,245309197,245309332⟩]
theorem checked50131 : checkPrefixCuts (2^48) 6574702593 10 Manual.Count131072.C050131.packed 64 cuts50131 = true := by
 decide +kernel
def pointBounds50131 : List (Nat × Nat × Nat) := [(6574725120,111689458939686,111689846080310)]
theorem point_links_checked50131 : (cuts50131.take 1).map (fun c => (6574702593-1+2*2^10*c.k,111689417669175+c.lower,111689804809775+c.upper)) = pointBounds50131 := by
 decide +kernel
def cuts50132 : List PrefixCut := [⟨48,187082460,187082565⟩,
⟨64,250441568,250441708⟩]
theorem checked50132 : checkPrefixCuts (2^48) 6574833665 10 Manual.Count131072.C050132.packed 64 cuts50132 = true := by
 decide +kernel
def pointBounds50132 : List (Nat × Nat × Nat) := [(6574931968,111689850060832,111690237201672)]
theorem point_links_checked50132 : (cuts50132.take 1).map (fun c => (6574833665-1+2*2^10*c.k,111689662978372+c.lower,111690050119107+c.upper)) = pointBounds50132 := by
 decide +kernel
def cuts50133 : List PrefixCut := [⟨64,247311462,247311604⟩]
theorem checked50133 : checkPrefixCuts (2^48) 6574964737 10 Manual.Count131072.C050133.packed 64 cuts50133 = true := by
 decide +kernel
def cuts50134 : List PrefixCut := [⟨21,81551348,81551394⟩,
⟨64,249789455,249789595⟩]
theorem checked50134 : checkPrefixCuts (2^48) 6575095809 10 Manual.Count131072.C050134.packed 64 cuts50134 = true := by
 decide +kernel
def pointBounds50134 : List (Nat × Nat × Nat) := [(6575138816,111690242282750,111690629423813)]
theorem point_links_checked50134 : (cuts50134.take 1).map (fun c => (6575095809-1+2*2^10*c.k,111690160731402+c.lower,111690547872419+c.upper)) = pointBounds50134 := by
 decide +kernel
def cuts50135 : List PrefixCut := [⟨58,223928677,223928802⟩,
⟨64,246402657,246402794⟩]
theorem checked50135 : checkPrefixCuts (2^48) 6575226881 10 Manual.Count131072.C050135.packed 64 cuts50135 = true := by
 decide +kernel
def pointBounds50135 : List (Nat × Nat × Nat) := [(6575345664,111690634449534,111691021590816)]
theorem point_links_checked50135 : (cuts50135.take 1).map (fun c => (6575226881-1+2*2^10*c.k,111690410520857+c.lower,111690797662014+c.upper)) = pointBounds50135 := by
 decide +kernel
def cuts50136 : List PrefixCut := [⟨64,246012477,246012618⟩]
theorem checked50136 : checkPrefixCuts (2^48) 6575357953 10 Manual.Count131072.C050136.packed 64 cuts50136 = true := by
 decide +kernel
def cuts50137 : List PrefixCut := [⟨31,123154237,123154305⟩,
⟨64,250887497,250887636⟩]
theorem checked50137 : checkPrefixCuts (2^48) 6575489025 10 Manual.Count131072.C050137.packed 64 cuts50137 = true := by
 decide +kernel
def pointBounds50137 : List (Nat × Nat × Nat) := [(6575552512,111691026090228,111691413231731)]
theorem point_links_checked50137 : (cuts50137.take 1).map (fun c => (6575489025-1+2*2^10*c.k,111690902935991+c.lower,111691290077426+c.upper)) = pointBounds50137 := by
 decide +kernel
def cuts50138 : List PrefixCut := [⟨64,246473543,246473685⟩]
theorem checked50138 : checkPrefixCuts (2^48) 6575620097 10 Manual.Count131072.C050138.packed 64 cuts50138 = true := by
 decide +kernel
def cuts50139 : List PrefixCut := [⟨4,16608322,16608331⟩,
⟨64,249892986,249893133⟩]
theorem checked50139 : checkPrefixCuts (2^48) 6575751169 10 Manual.Count131072.C050139.packed 64 cuts50139 = true := by
 decide +kernel
def pointBounds50139 : List (Nat × Nat × Nat) := [(6575759360,111691416905353,111691804047078)]
theorem point_links_checked50139 : (cuts50139.take 1).map (fun c => (6575751169-1+2*2^10*c.k,111691400297031+c.lower,111691787438747+c.upper)) = pointBounds50139 := by
 decide +kernel
def cuts50140 : List PrefixCut := [⟨41,159572772,159572858⟩,
⟨64,248732313,248732454⟩]
theorem checked50140 : checkPrefixCuts (2^48) 6575882241 10 Manual.Count131072.C050140.packed 64 cuts50140 = true := by
 decide +kernel
def pointBounds50140 : List (Nat × Nat × Nat) := [(6575966208,111691809762789,111692196904738)]
theorem point_links_checked50140 : (cuts50140.take 1).map (fun c => (6575882241-1+2*2^10*c.k,111691650190017+c.lower,111692037331880+c.upper)) = pointBounds50140 := by
 decide +kernel
def cuts50141 : List PrefixCut := [⟨64,248556131,248556273⟩]
theorem checked50141 : checkPrefixCuts (2^48) 6576013313 10 Manual.Count131072.C050141.packed 64 cuts50141 = true := by
 decide +kernel
def cuts50142 : List PrefixCut := [⟨14,55557423,55557454⟩,
⟨64,246025886,246026027⟩]
theorem checked50142 : checkPrefixCuts (2^48) 6576144385 10 Manual.Count131072.C050142.packed 64 cuts50142 = true := by
 decide +kernel
def pointBounds50142 : List (Nat × Nat × Nat) := [(6576173056,111692203035884,111692590178061)]
theorem point_links_checked50142 : (cuts50142.take 1).map (fun c => (6576144385-1+2*2^10*c.k,111692147478461+c.lower,111692534620607+c.upper)) = pointBounds50142 := by
 decide +kernel
def cuts50143 : List PrefixCut := [⟨51,198768911,198769020⟩,
⟨64,246534606,246534742⟩]
theorem checked50143 : checkPrefixCuts (2^48) 6576275457 10 Manual.Count131072.C050143.packed 64 cuts50143 = true := by
 decide +kernel
def pointBounds50143 : List (Nat × Nat × Nat) := [(6576379904,111692592273258,111692979415654)]
theorem point_links_checked50143 : (cuts50143.take 1).map (fun c => (6576275457-1+2*2^10*c.k,111692393504347+c.lower,111692780646634+c.upper)) = pointBounds50143 := by
 decide +kernel
def cuts50144 : List PrefixCut := [⟨64,247428464,247428605⟩]
theorem checked50144 : checkPrefixCuts (2^48) 6576406529 10 Manual.Count131072.C050144.packed 64 cuts50144 = true := by
 decide +kernel
def cuts50145 : List PrefixCut := [⟨24,90221769,90221821⟩,
⟨64,245155144,245155284⟩]
theorem checked50145 : checkPrefixCuts (2^48) 6576537601 10 Manual.Count131072.C050145.packed 64 cuts50145 = true := by
 decide +kernel
def pointBounds50145 : List (Nat × Nat × Nat) := [(6576586752,111692977689186,111693364831802)]
theorem point_links_checked50145 : (cuts50145.take 1).map (fun c => (6576537601-1+2*2^10*c.k,111692887467417+c.lower,111693274609981+c.upper)) = pointBounds50145 := by
 decide +kernel
def cuts50146 : List PrefixCut := [⟨61,236419455,236419584⟩,
⟨64,248402944,248403080⟩]
theorem checked50146 : checkPrefixCuts (2^48) 6576668673 10 Manual.Count131072.C050146.packed 64 cuts50146 = true := by
 decide +kernel
def pointBounds50146 : List (Nat × Nat × Nat) := [(6576793600,111693369042016,111693756184849)]
theorem point_links_checked50146 : (cuts50146.take 1).map (fun c => (6576668673-1+2*2^10*c.k,111693132622561+c.lower,111693519765265+c.upper)) = pointBounds50146 := by
 decide +kernel
def cuts50147 : List PrefixCut := [⟨64,248783197,248783332⟩]
theorem checked50147 : checkPrefixCuts (2^48) 6576799745 10 Manual.Count131072.C050147.packed 64 cuts50147 = true := by
 decide +kernel
def cuts50148 : List PrefixCut := [⟨34,132585338,132585410⟩,
⟨64,248521460,248521599⟩]
theorem checked50148 : checkPrefixCuts (2^48) 6576930817 10 Manual.Count131072.C050148.packed 64 cuts50148 = true := by
 decide +kernel
def pointBounds50148 : List (Nat × Nat × Nat) := [(6577000448,111693762394040,111694149537087)]
theorem point_links_checked50148 : (cuts50148.take 1).map (fun c => (6576930817-1+2*2^10*c.k,111693629808702+c.lower,111694016951677+c.upper)) = pointBounds50148 := by
 decide +kernel
def cuts50149 : List PrefixCut := [⟨64,251212647,251212788⟩]
theorem checked50149 : checkPrefixCuts (2^48) 6577061889 10 Manual.Count131072.C050149.packed 64 cuts50149 = true := by
 decide +kernel
def cuts50150 : List PrefixCut := [⟨7,27517539,27517553⟩,
⟨64,248554350,248554497⟩]
theorem checked50150 : checkPrefixCuts (2^48) 6577192961 10 Manual.Count131072.C050150.packed 64 cuts50150 = true := by
 decide +kernel
def pointBounds50150 : List (Nat × Nat × Nat) := [(6577207296,111694157060348,111694544203617)]
theorem point_links_checked50150 : (cuts50150.take 1).map (fun c => (6577192961-1+2*2^10*c.k,111694129542809+c.lower,111694516686064+c.upper)) = pointBounds50150 := by
 decide +kernel
def cuts50151 : List PrefixCut := [⟨44,172761201,172761298⟩,
⟨64,247351183,247351323⟩]
theorem checked50151 : checkPrefixCuts (2^48) 6577324033 10 Manual.Count131072.C050151.packed 64 cuts50151 = true := by
 decide +kernel
def pointBounds50151 : List (Nat × Nat × Nat) := [(6577414144,111694550858360,111694938001859)]
theorem point_links_checked50151 : (cuts50151.take 1).map (fun c => (6577324033-1+2*2^10*c.k,111694378097159+c.lower,111694765240561+c.upper)) = pointBounds50151 := by
 decide +kernel
def cuts50152 : List PrefixCut := [⟨64,251839550,251839687⟩]
theorem checked50152 : checkPrefixCuts (2^48) 6577455105 10 Manual.Count131072.C050152.packed 64 cuts50152 = true := by
 decide +kernel
def cuts50153 : List PrefixCut := [⟨17,67912372,67912414⟩,
⟨64,247683664,247683806⟩]
theorem checked50153 : checkPrefixCuts (2^48) 6577586177 10 Manual.Count131072.C050153.packed 64 cuts50153 = true := by
 decide +kernel
def pointBounds50153 : List (Nat × Nat × Nat) := [(6577620992,111694945200264,111695332343985)]
theorem point_links_checked50153 : (cuts50153.take 1).map (fun c => (6577586177-1+2*2^10*c.k,111694877287892+c.lower,111695264431571+c.upper)) = pointBounds50153 := by
 decide +kernel
def cuts50154 : List PrefixCut := [⟨54,211862339,211862459⟩,
⟨64,249433188,249433329⟩]
theorem checked50154 : checkPrefixCuts (2^48) 6577717249 10 Manual.Count131072.C050154.packed 64 cuts50154 = true := by
 decide +kernel
def pointBounds50154 : List (Nat × Nat × Nat) := [(6577827840,111695336833895,111695723977836)]
theorem point_links_checked50154 : (cuts50154.take 1).map (fun c => (6577717249-1+2*2^10*c.k,111695124971556+c.lower,111695512115377+c.upper)) = pointBounds50154 := by
 decide +kernel
def cuts50155 : List PrefixCut := [⟨64,248572376,248572512⟩]
theorem checked50155 : checkPrefixCuts (2^48) 6577848321 10 Manual.Count131072.C050155.packed 64 cuts50155 = true := by
 decide +kernel
def cuts50156 : List PrefixCut := [⟨27,104451124,104451184⟩,
⟨64,247369293,247369434⟩]
theorem checked50156 : checkPrefixCuts (2^48) 6577979393 10 Manual.Count131072.C050156.packed 64 cuts50156 = true := by
 decide +kernel
def pointBounds50156 : List (Nat × Nat × Nat) := [(6578034688,111695727428244,111696114572402)]
theorem point_links_checked50156 : (cuts50156.take 1).map (fun c => (6577979393-1+2*2^10*c.k,111695622977120+c.lower,111696010121218+c.upper)) = pointBounds50156 := by
 decide +kernel
def cuts50157 : List PrefixCut := [⟨64,248134573,248134718⟩]
theorem checked50157 : checkPrefixCuts (2^48) 6578110465 10 Manual.Count131072.C050157.packed 64 cuts50157 = true := by
 decide +kernel
def pointBounds50157 : List (Nat × Nat × Nat) := [(6578241536,111696118480986,111696505625370)]
theorem point_links_checked50157 : (cuts50157.take 1).map (fun c => (6578110465-1+2*2^10*c.k,111695870346413+c.lower,111696257490652+c.upper)) = pointBounds50157 := by
 decide +kernel
def cuts50158 : List PrefixCut := [⟨64,250397421,250397560⟩]
theorem checked50158 : checkPrefixCuts (2^48) 6578241537 10 Manual.Count131072.C050158.packed 64 cuts50158 = true := by
 decide +kernel
def cuts50159 : List PrefixCut := [⟨37,145520878,145520958⟩,
⟨64,249707828,249707969⟩]
theorem checked50159 : checkPrefixCuts (2^48) 6578372609 10 Manual.Count131072.C050159.packed 64 cuts50159 = true := by
 decide +kernel
def pointBounds50159 : List (Nat × Nat × Nat) := [(6578448384,111696514399285,111696901543888)]
theorem point_links_checked50159 : (cuts50159.take 1).map (fun c => (6578372609-1+2*2^10*c.k,111696368878407+c.lower,111696756022930+c.upper)) = pointBounds50159 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000004
