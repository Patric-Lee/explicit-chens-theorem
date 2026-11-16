import PlattAssemblyKernel
import PlattCertificates.Count131072.C050160
import PlattCertificates.Count131072.C050161
import PlattCertificates.Count131072.C050162
import PlattCertificates.Count131072.C050163
import PlattCertificates.Count131072.C050164
import PlattCertificates.Count131072.C050165
import PlattCertificates.Count131072.C050166
import PlattCertificates.Count131072.C050167
import PlattCertificates.Count131072.C050168
import PlattCertificates.Count131072.C050169
import PlattCertificates.Count131072.C050170
import PlattCertificates.Count131072.C050171
import PlattCertificates.Count131072.C050172
import PlattCertificates.Count131072.C050173
import PlattCertificates.Count131072.C050174
import PlattCertificates.Count131072.C050175
import PlattCertificates.Count131072.C050176
import PlattCertificates.Count131072.C050177
import PlattCertificates.Count131072.C050178
import PlattCertificates.Count131072.C050179
import PlattCertificates.Count131072.C050180
import PlattCertificates.Count131072.C050181
import PlattCertificates.Count131072.C050182
import PlattCertificates.Count131072.C050183
import PlattCertificates.Count131072.C050184
import PlattCertificates.Count131072.C050185
import PlattCertificates.Count131072.C050186
import PlattCertificates.Count131072.C050187
import PlattCertificates.Count131072.C050188
import PlattCertificates.Count131072.C050189
import PlattCertificates.Count131072.C050190
import PlattCertificates.Count131072.C050191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50160 : List PrefixCut := [⟨64,248504835,248504983⟩]
theorem checked50160 : checkPrefixCuts (2^48) 6578503681 10 Manual.Count131072.C050160.packed 64 cuts50160 = true := by
 decide +kernel
def cuts50161 : List PrefixCut := [⟨10,37951315,37951337⟩,
⟨64,248414281,248414421⟩]
theorem checked50161 : checkPrefixCuts (2^48) 6578634753 10 Manual.Count131072.C050161.packed 64 cuts50161 = true := by
 decide +kernel
def pointBounds50161 : List (Nat × Nat × Nat) := [(6578655232,111696905042385,111697292187219)]
theorem point_links_checked50161 : (cuts50161.take 1).map (fun c => (6578634753-1+2*2^10*c.k,111696867091070+c.lower,111697254235882+c.upper)) = pointBounds50161 := by
 decide +kernel
def cuts50162 : List PrefixCut := [⟨47,180082287,180082389⟩,
⟨64,245927829,245927968⟩]
theorem checked50162 : checkPrefixCuts (2^48) 6578765825 10 Manual.Count131072.C050162.packed 64 cuts50162 = true := by
 decide +kernel
def pointBounds50162 : List (Nat × Nat × Nat) := [(6578862080,111697295587638,111697682732692)]
theorem point_links_checked50162 : (cuts50162.take 1).map (fun c => (6578765825-1+2*2^10*c.k,111697115505351+c.lower,111697502650303+c.upper)) = pointBounds50162 := by
 decide +kernel
def cuts50163 : List PrefixCut := [⟨64,247377568,247377711⟩]
theorem checked50163 : checkPrefixCuts (2^48) 6578896897 10 Manual.Count131072.C050163.packed 64 cuts50163 = true := by
 decide +kernel
def cuts50164 : List PrefixCut := [⟨20,75427356,75427400⟩,
⟨64,247287073,247287213⟩]
theorem checked50164 : checkPrefixCuts (2^48) 6579027969 10 Manual.Count131072.C050164.packed 64 cuts50164 = true := by
 decide +kernel
def pointBounds50164 : List (Nat × Nat × Nat) := [(6579068928,111697684238104,111698071383382)]
theorem point_links_checked50164 : (cuts50164.take 1).map (fun c => (6579027969-1+2*2^10*c.k,111697608810748+c.lower,111697995955982+c.upper)) = pointBounds50164 := by
 decide +kernel
def cuts50165 : List PrefixCut := [⟨57,221997998,221998125⟩,
⟨64,248736750,248736892⟩]
theorem checked50165 : checkPrefixCuts (2^48) 6579159041 10 Manual.Count131072.C050165.packed 64 cuts50165 = true := by
 decide +kernel
def pointBounds50165 : List (Nat × Nat × Nat) := [(6579275776,111698078095819,111698465241320)]
theorem point_links_checked50165 : (cuts50165.take 1).map (fun c => (6579159041-1+2*2^10*c.k,111697856097821+c.lower,111698243243195+c.upper)) = pointBounds50165 := by
 decide +kernel
def cuts50166 : List PrefixCut := [⟨64,249245191,249245334⟩]
theorem checked50166 : checkPrefixCuts (2^48) 6579290113 10 Manual.Count131072.C050166.packed 64 cuts50166 = true := by
 decide +kernel
def cuts50167 : List PrefixCut := [⟨30,116577959,116578029⟩,
⟨64,247871240,247871386⟩]
theorem checked50167 : checkPrefixCuts (2^48) 6579421185 10 Manual.Count131072.C050167.packed 64 cuts50167 = true := by
 decide +kernel
def pointBounds50167 : List (Nat × Nat × Nat) := [(6579482624,111698470657721,111698857803450)]
theorem point_links_checked50167 : (cuts50167.take 1).map (fun c => (6579421185-1+2*2^10*c.k,111698354079762+c.lower,111698741225421+c.upper)) = pointBounds50167 := by
 decide +kernel
def cuts50168 : List PrefixCut := [⟨64,248080223,248080367⟩]
theorem checked50168 : checkPrefixCuts (2^48) 6579552257 10 Manual.Count131072.C050168.packed 64 cuts50168 = true := by
 decide +kernel
def cuts50169 : List PrefixCut := [⟨3,12277682,12277688⟩,
⟨64,246150223,246150360⟩]
theorem checked50169 : checkPrefixCuts (2^48) 6579683329 10 Manual.Count131072.C050169.packed 64 cuts50169 = true := by
 decide +kernel
def pointBounds50169 : List (Nat × Nat × Nat) := [(6579689472,111698862308907,111699249454862)]
theorem point_links_checked50169 : (cuts50169.take 1).map (fun c => (6579683329-1+2*2^10*c.k,111698850031225+c.lower,111699237177174+c.upper)) = pointBounds50169 := by
 decide +kernel
def cuts50170 : List PrefixCut := [⟨40,155456284,155456375⟩,
⟨64,248712013,248712157⟩]
theorem checked50170 : checkPrefixCuts (2^48) 6579814401 10 Manual.Count131072.C050170.packed 64 cuts50170 = true := by
 decide +kernel
def pointBounds50170 : List (Nat × Nat × Nat) := [(6579896320,111699251637732,111699638783909)]
theorem point_links_checked50170 : (cuts50170.take 1).map (fun c => (6579814401-1+2*2^10*c.k,111699096181448+c.lower,111699483327534+c.upper)) = pointBounds50170 := by
 decide +kernel
def cuts50171 : List PrefixCut := [⟨64,243702084,243702230⟩]
theorem checked50171 : checkPrefixCuts (2^48) 6579945473 10 Manual.Count131072.C050171.packed 64 cuts50171 = true := by
 decide +kernel
def cuts50172 : List PrefixCut := [⟨13,52358749,52358778⟩,
⟨64,251354233,251354376⟩]
theorem checked50172 : checkPrefixCuts (2^48) 6580076545 10 Manual.Count131072.C050172.packed 64 cuts50172 = true := by
 decide +kernel
def pointBounds50172 : List (Nat × Nat × Nat) := [(6580103168,111699640954294,111700028100699)]
theorem point_links_checked50172 : (cuts50172.take 1).map (fun c => (6580076545-1+2*2^10*c.k,111699588595545+c.lower,111699975741921+c.upper)) = pointBounds50172 := by
 decide +kernel
def cuts50173 : List PrefixCut := [⟨50,192447666,192447778⟩,
⟨64,247328290,247328433⟩]
theorem checked50173 : checkPrefixCuts (2^48) 6580207617 10 Manual.Count131072.C050173.packed 64 cuts50173 = true := by
 decide +kernel
def pointBounds50173 : List (Nat × Nat × Nat) := [(6580310016,111700032397444,111700419544075)]
theorem point_links_checked50173 : (cuts50173.take 1).map (fun c => (6580207617-1+2*2^10*c.k,111699839949778+c.lower,111700227096297+c.upper)) = pointBounds50173 := by
 decide +kernel
def cuts50174 : List PrefixCut := [⟨64,246382332,246382475⟩]
theorem checked50174 : checkPrefixCuts (2^48) 6580338689 10 Manual.Count131072.C050174.packed 64 cuts50174 = true := by
 decide +kernel
def cuts50175 : List PrefixCut := [⟨23,93290381,93290432⟩,
⟨64,249884912,249885050⟩]
theorem checked50175 : checkPrefixCuts (2^48) 6580469761 10 Manual.Count131072.C050175.packed 64 cuts50175 = true := by
 decide +kernel
def pointBounds50175 : List (Nat × Nat × Nat) := [(6580516864,111700426950781,111700814097637)]
theorem point_links_checked50175 : (cuts50175.take 1).map (fun c => (6580469761-1+2*2^10*c.k,111700333660400+c.lower,111700720807205+c.upper)) = pointBounds50175 := by
 decide +kernel
def cuts50176 : List PrefixCut := [⟨60,230931604,230931734⟩,
⟨64,245902017,245902156⟩]
theorem checked50176 : checkPrefixCuts (2^48) 6580600833 10 Manual.Count131072.C050176.packed 64 cuts50176 = true := by
 decide +kernel
def pointBounds50176 : List (Nat × Nat × Nat) := [(6580723712,111700814476916,111701201623989)]
theorem point_links_checked50176 : (cuts50176.take 1).map (fun c => (6580600833-1+2*2^10*c.k,111700583545312+c.lower,111700970692255+c.upper)) = pointBounds50176 := by
 decide +kernel
def cuts50177 : List PrefixCut := [⟨64,249318885,249319021⟩]
theorem checked50177 : checkPrefixCuts (2^48) 6580731905 10 Manual.Count131072.C050177.packed 64 cuts50177 = true := by
 decide +kernel
def cuts50178 : List PrefixCut := [⟨33,127459117,127459190⟩,
⟨64,248030804,248030949⟩]
theorem checked50178 : checkPrefixCuts (2^48) 6580862977 10 Manual.Count131072.C050178.packed 64 cuts50178 = true := by
 decide +kernel
def pointBounds50178 : List (Nat × Nat × Nat) := [(6580930560,111701206225331,111701593372622)]
theorem point_links_checked50178 : (cuts50178.take 1).map (fun c => (6580862977-1+2*2^10*c.k,111701078766214+c.lower,111701465913432+c.upper)) = pointBounds50178 := by
 decide +kernel
def cuts50179 : List PrefixCut := [⟨64,245160229,245160371⟩]
theorem checked50179 : checkPrefixCuts (2^48) 6580994049 10 Manual.Count131072.C050179.packed 64 cuts50179 = true := by
 decide +kernel
def cuts50180 : List PrefixCut := [⟨6,23651803,23651816⟩,
⟨64,248919074,248919215⟩]
theorem checked50180 : checkPrefixCuts (2^48) 6581125121 10 Manual.Count131072.C050180.packed 64 cuts50180 = true := by
 decide +kernel
def pointBounds50180 : List (Nat × Nat × Nat) := [(6581137408,111701595609050,111701982756568)]
theorem point_links_checked50180 : (cuts50180.take 1).map (fun c => (6581125121-1+2*2^10*c.k,111701571957247+c.lower,111701959104752+c.upper)) = pointBounds50180 := by
 decide +kernel
def cuts50181 : List PrefixCut := [⟨43,167311885,167311981⟩,
⟨64,250026093,250026237⟩]
theorem checked50181 : checkPrefixCuts (2^48) 6581256193 10 Manual.Count131072.C050181.packed 64 cuts50181 = true := by
 decide +kernel
def pointBounds50181 : List (Nat × Nat × Nat) := [(6581344256,111701988188206,111702375335948)]
theorem point_links_checked50181 : (cuts50181.take 1).map (fun c => (6581256193-1+2*2^10*c.k,111701820876321+c.lower,111702208023967+c.upper)) = pointBounds50181 := by
 decide +kernel
def cuts50182 : List PrefixCut := [⟨64,247070131,247070271⟩]
theorem checked50182 : checkPrefixCuts (2^48) 6581387265 10 Manual.Count131072.C050182.packed 64 cuts50182 = true := by
 decide +kernel
def cuts50183 : List PrefixCut := [⟨16,61969912,61969946⟩,
⟨64,249802321,249802460⟩]
theorem checked50183 : checkPrefixCuts (2^48) 6581518337 10 Manual.Count131072.C050183.packed 64 cuts50183 = true := by
 decide +kernel
def pointBounds50183 : List (Nat × Nat × Nat) := [(6581551104,111702379942457,111702767090421)]
theorem point_links_checked50183 : (cuts50183.take 1).map (fun c => (6581518337-1+2*2^10*c.k,111702317972545+c.lower,111702705120475+c.upper)) = pointBounds50183 := by
 decide +kernel
def cuts50184 : List PrefixCut := [⟨53,202968710,202968825⟩,
⟨64,247530717,247530857⟩]
theorem checked50184 : checkPrefixCuts (2^48) 6581649409 10 Manual.Count131072.C050184.packed 64 cuts50184 = true := by
 decide +kernel
def pointBounds50184 : List (Nat × Nat × Nat) := [(6581757952,111702770743576,111703157891760)]
theorem point_links_checked50184 : (cuts50184.take 1).map (fun c => (6581649409-1+2*2^10*c.k,111702567774866+c.lower,111702954922935+c.upper)) = pointBounds50184 := by
 decide +kernel
def cuts50185 : List PrefixCut := [⟨64,246200057,246200202⟩]
theorem checked50185 : checkPrefixCuts (2^48) 6581780481 10 Manual.Count131072.C050185.packed 64 cuts50185 = true := by
 decide +kernel
def cuts50186 : List PrefixCut := [⟨26,100026732,100026793⟩,
⟨64,248076789,248076936⟩]
theorem checked50186 : checkPrefixCuts (2^48) 6581911553 10 Manual.Count131072.C050186.packed 64 cuts50186 = true := by
 decide +kernel
def pointBounds50186 : List (Nat × Nat × Nat) := [(6581964800,111703161532372,111703548680787)]
theorem point_links_checked50186 : (cuts50186.take 1).map (fun c => (6581911553-1+2*2^10*c.k,111703061505640+c.lower,111703448653994+c.upper)) = pointBounds50186 := by
 decide +kernel
def cuts50187 : List PrefixCut := [⟨63,245078440,245078578⟩,
⟨64,249055419,249055560⟩]
theorem checked50187 : checkPrefixCuts (2^48) 6582042625 10 Manual.Count131072.C050187.packed 64 cuts50187 = true := by
 decide +kernel
def pointBounds50187 : List (Nat × Nat × Nat) := [(6582171648,111703554660869,111703941809508)]
theorem point_links_checked50187 : (cuts50187.take 1).map (fun c => (6582042625-1+2*2^10*c.k,111703309582429+c.lower,111703696730930+c.upper)) = pointBounds50187 := by
 decide +kernel
def cuts50188 : List PrefixCut := [⟨64,245501156,245501297⟩]
theorem checked50188 : checkPrefixCuts (2^48) 6582173697 10 Manual.Count131072.C050188.packed 64 cuts50188 = true := by
 decide +kernel
def cuts50189 : List PrefixCut := [⟨36,139361751,139361830⟩,
⟨64,246821894,246822034⟩]
theorem checked50189 : checkPrefixCuts (2^48) 6582304769 10 Manual.Count131072.C050189.packed 64 cuts50189 = true := by
 decide +kernel
def pointBounds50189 : List (Nat × Nat × Nat) := [(6582378496,111703943500755,111704330649617)]
theorem point_links_checked50189 : (cuts50189.take 1).map (fun c => (6582304769-1+2*2^10*c.k,111703804139004+c.lower,111704191287787+c.upper)) = pointBounds50189 := by
 decide +kernel
def cuts50190 : List PrefixCut := [⟨64,249211597,249211737⟩]
theorem checked50190 : checkPrefixCuts (2^48) 6582435841 10 Manual.Count131072.C050190.packed 64 cuts50190 = true := by
 decide +kernel
def cuts50191 : List PrefixCut := [⟨9,34764368,34764388⟩,
⟨64,247966576,247966723⟩]
theorem checked50191 : checkPrefixCuts (2^48) 6582566913 10 Manual.Count131072.C050191.packed 64 cuts50191 = true := by
 decide +kernel
def pointBounds50191 : List (Nat × Nat × Nat) := [(6582585344,111704334936863,111704722085946)]
theorem point_links_checked50191 : (cuts50191.take 1).map (fun c => (6582566913-1+2*2^10*c.k,111704300172495+c.lower,111704687321558+c.upper)) = pointBounds50191 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000005
