import PlattAssemblyKernel
import PlattCertificates.Count131072.C069152
import PlattCertificates.Count131072.C069153
import PlattCertificates.Count131072.C069154
import PlattCertificates.Count131072.C069155
import PlattCertificates.Count131072.C069156
import PlattCertificates.Count131072.C069157
import PlattCertificates.Count131072.C069158
import PlattCertificates.Count131072.C069159
import PlattCertificates.Count131072.C069160
import PlattCertificates.Count131072.C069161
import PlattCertificates.Count131072.C069162
import PlattCertificates.Count131072.C069163
import PlattCertificates.Count131072.C069164
import PlattCertificates.Count131072.C069165
import PlattCertificates.Count131072.C069166
import PlattCertificates.Count131072.C069167
import PlattCertificates.Count131072.C069168
import PlattCertificates.Count131072.C069169
import PlattCertificates.Count131072.C069170
import PlattCertificates.Count131072.C069171
import PlattCertificates.Count131072.C069172
import PlattCertificates.Count131072.C069173
import PlattCertificates.Count131072.C069174
import PlattCertificates.Count131072.C069175
import PlattCertificates.Count131072.C069176
import PlattCertificates.Count131072.C069177
import PlattCertificates.Count131072.C069178
import PlattCertificates.Count131072.C069179
import PlattCertificates.Count131072.C069180
import PlattCertificates.Count131072.C069181
import PlattCertificates.Count131072.C069182
import PlattCertificates.Count131072.C069183
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000286
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69152 : List PrefixCut := [⟨57,158587787,158587880⟩,
⟨64,176901765,176901871⟩]
theorem checked69152 : checkPrefixCuts (2^48) 9067823105 10 Manual.Count131072.C069152.packed 64 cuts69152 = true := by
 decide +kernel
def pointBounds69152 : List (Nat × Nat × Nat) := [(9067939840,115664389264831,115664778682234)]
theorem point_links_checked69152 : (cuts69152.take 1).map (fun c => (9067823105-1+2*2^10*c.k,115664230677044+c.lower,115664620094354+c.upper)) = pointBounds69152 := by
 decide +kernel
def cuts69153 : List PrefixCut := [⟨64,178854737,178854843⟩]
theorem checked69153 : checkPrefixCuts (2^48) 9067954177 10 Manual.Count131072.C069153.packed 64 cuts69153 = true := by
 decide +kernel
def cuts69154 : List PrefixCut := [⟨64,179286720,179286825⟩]
theorem checked69154 : checkPrefixCuts (2^48) 9068085249 10 Manual.Count131072.C069154.packed 64 cuts69154 = true := by
 decide +kernel
def cuts69155 : List PrefixCut := [⟨4,11143255,11143260⟩,
⟨64,175093802,175093902⟩]
theorem checked69155 : checkPrefixCuts (2^48) 9068216321 10 Manual.Count131072.C069155.packed 64 cuts69155 = true := by
 decide +kernel
def pointBounds69155 : List (Nat × Nat × Nat) := [(9068224512,115664776863521,115665166281153)]
theorem point_links_checked69155 : (cuts69155.take 1).map (fun c => (9068216321-1+2*2^10*c.k,115664765720266+c.lower,115665155137893+c.upper)) = pointBounds69155 := by
 decide +kernel
def cuts69156 : List PrefixCut := [⟨64,176270752,176270859⟩]
theorem checked69156 : checkPrefixCuts (2^48) 9068347393 10 Manual.Count131072.C069156.packed 64 cuts69156 = true := by
 decide +kernel
def cuts69157 : List PrefixCut := [⟨15,40660788,40660812⟩,
⟨64,174933542,174933648⟩]
theorem checked69157 : checkPrefixCuts (2^48) 9068478465 10 Manual.Count131072.C069157.packed 64 cuts69157 = true := by
 decide +kernel
def pointBounds69157 : List (Nat × Nat × Nat) := [(9068509184,115665157745608,115665547163466)]
theorem point_links_checked69157 : (cuts69157.take 1).map (fun c => (9068478465-1+2*2^10*c.k,115665117084820+c.lower,115665506502654+c.upper)) = pointBounds69157 := by
 decide +kernel
def cuts69158 : List PrefixCut := [⟨64,175738001,175738099⟩]
theorem checked69158 : checkPrefixCuts (2^48) 9068609537 10 Manual.Count131072.C069158.packed 64 cuts69158 = true := by
 decide +kernel
def cuts69159 : List PrefixCut := [⟨26,73652785,73652828⟩,
⟨64,179801410,179801519⟩]
theorem checked69159 : checkPrefixCuts (2^48) 9068740609 10 Manual.Count131072.C069159.packed 64 cuts69159 = true := by
 decide +kernel
def pointBounds69159 : List (Nat × Nat × Nat) := [(9068793856,115665541409148,115665930827229)]
theorem point_links_checked69159 : (cuts69159.take 1).map (fun c => (9068740609-1+2*2^10*c.k,115665467756363+c.lower,115665857174401+c.upper)) = pointBounds69159 := by
 decide +kernel
def cuts69160 : List PrefixCut := [⟨64,173653422,173653530⟩]
theorem checked69160 : checkPrefixCuts (2^48) 9068871681 10 Manual.Count131072.C069160.packed 64 cuts69160 = true := by
 decide +kernel
def cuts69161 : List PrefixCut := [⟨37,102452803,102452867⟩,
⟨64,177685703,177685809⟩]
theorem checked69161 : checkPrefixCuts (2^48) 9069002753 10 Manual.Count131072.C069161.packed 64 cuts69161 = true := by
 decide +kernel
def pointBounds69161 : List (Nat × Nat × Nat) := [(9069078528,115665923663998,115666313082317)]
theorem point_links_checked69161 : (cuts69161.take 1).map (fun c => (9069002753-1+2*2^10*c.k,115665821211195+c.lower,115666210629450+c.upper)) = pointBounds69161 := by
 decide +kernel
def cuts69162 : List PrefixCut := [⟨64,180538474,180538576⟩]
theorem checked69162 : checkPrefixCuts (2^48) 9069133825 10 Manual.Count131072.C069162.packed 64 cuts69162 = true := by
 decide +kernel
def cuts69163 : List PrefixCut := [⟨48,134137436,134137516⟩,
⟨64,178984079,178984185⟩]
theorem checked69163 : checkPrefixCuts (2^48) 9069264897 10 Manual.Count131072.C069163.packed 64 cuts69163 = true := by
 decide +kernel
def pointBounds69163 : List (Nat × Nat × Nat) := [(9069363200,115666313572808,115666702991351)]
theorem point_links_checked69163 : (cuts69163.take 1).map (fun c => (9069264897-1+2*2^10*c.k,115666179435372+c.lower,115666568853835+c.upper)) = pointBounds69163 := by
 decide +kernel
def cuts69164 : List PrefixCut := [⟨64,179664263,179664367⟩]
theorem checked69164 : checkPrefixCuts (2^48) 9069395969 10 Manual.Count131072.C069164.packed 64 cuts69164 = true := by
 decide +kernel
def cuts69165 : List PrefixCut := [⟨59,163306300,163306397⟩,
⟨64,176992648,176992753⟩]
theorem checked69165 : checkPrefixCuts (2^48) 9069527041 10 Manual.Count131072.C069165.packed 64 cuts69165 = true := by
 decide +kernel
def pointBounds69165 : List (Nat × Nat × Nat) := [(9069647872,115666701390014,115667090808784)]
theorem point_links_checked69165 : (cuts69165.take 1).map (fun c => (9069527041-1+2*2^10*c.k,115666538083714+c.lower,115666927502387+c.upper)) = pointBounds69165 := by
 decide +kernel
def cuts69166 : List PrefixCut := [⟨64,177765970,177766069⟩]
theorem checked69166 : checkPrefixCuts (2^48) 9069658113 10 Manual.Count131072.C069166.packed 64 cuts69166 = true := by
 decide +kernel
def cuts69167 : List PrefixCut := [⟨64,176739259,176739366⟩]
theorem checked69167 : checkPrefixCuts (2^48) 9069789185 10 Manual.Count131072.C069167.packed 64 cuts69167 = true := by
 decide +kernel
def cuts69168 : List PrefixCut := [⟨6,16385883,16385893⟩,
⟨64,177791855,177791962⟩]
theorem checked69168 : checkPrefixCuts (2^48) 9069920257 10 Manual.Count131072.C069168.packed 64 cuts69168 = true := by
 decide +kernel
def pointBounds69168 : List (Nat × Nat × Nat) := [(9069932544,115667085967474,115667475386468)]
theorem point_links_checked69168 : (cuts69168.take 1).map (fun c => (9069920257-1+2*2^10*c.k,115667069581591+c.lower,115667459000575+c.upper)) = pointBounds69168 := by
 decide +kernel
def cuts69169 : List PrefixCut := [⟨64,174127380,174127482⟩]
theorem checked69169 : checkPrefixCuts (2^48) 9070051329 10 Manual.Count131072.C069169.packed 64 cuts69169 = true := by
 decide +kernel
def cuts69170 : List PrefixCut := [⟨17,46239071,46239098⟩,
⟨64,175924759,175924859⟩]
theorem checked69170 : checkPrefixCuts (2^48) 9070182401 10 Manual.Count131072.C069170.packed 64 cuts69170 = true := by
 decide +kernel
def pointBounds69170 : List (Nat × Nat × Nat) := [(9070217216,115667467739897,115667857159117)]
theorem point_links_checked69170 : (cuts69170.take 1).map (fun c => (9070182401-1+2*2^10*c.k,115667421500826+c.lower,115667810920019+c.upper)) = pointBounds69170 := by
 decide +kernel
def cuts69171 : List PrefixCut := [⟨64,175922220,175922321⟩]
theorem checked69171 : checkPrefixCuts (2^48) 9070313473 10 Manual.Count131072.C069171.packed 64 cuts69171 = true := by
 decide +kernel
def cuts69172 : List PrefixCut := [⟨28,77673084,77673130⟩,
⟨64,178774599,178774701⟩]
theorem checked69172 : checkPrefixCuts (2^48) 9070444545 10 Manual.Count131072.C069172.packed 64 cuts69172 = true := by
 decide +kernel
def pointBounds69172 : List (Nat × Nat × Nat) := [(9070501888,115667851020889,115668240440329)]
theorem point_links_checked69172 : (cuts69172.take 1).map (fun c => (9070444545-1+2*2^10*c.k,115667773347805+c.lower,115668162767199+c.upper)) = pointBounds69172 := by
 decide +kernel
def cuts69173 : List PrefixCut := [⟨64,175917128,175917232⟩]
theorem checked69173 : checkPrefixCuts (2^48) 9070575617 10 Manual.Count131072.C069173.packed 64 cuts69173 = true := by
 decide +kernel
def cuts69174 : List PrefixCut := [⟨39,109136233,109136298⟩,
⟨64,177993659,177993769⟩]
theorem checked69174 : checkPrefixCuts (2^48) 9070706689 10 Manual.Count131072.C069174.packed 64 cuts69174 = true := by
 decide +kernel
def pointBounds69174 : List (Nat × Nat × Nat) := [(9070786560,115668237175765,115668626595430)]
theorem point_links_checked69174 : (cuts69174.take 1).map (fun c => (9070706689-1+2*2^10*c.k,115668128039532+c.lower,115668517459132+c.upper)) = pointBounds69174 := by
 decide +kernel
def cuts69175 : List PrefixCut := [⟨64,179046130,179046237⟩]
theorem checked69175 : checkPrefixCuts (2^48) 9070837761 10 Manual.Count131072.C069175.packed 64 cuts69175 = true := by
 decide +kernel
def cuts69176 : List PrefixCut := [⟨50,137246248,137246320⟩,
⟨64,176468044,176468139⟩]
theorem checked69176 : checkPrefixCuts (2^48) 9070968833 10 Manual.Count131072.C069176.packed 64 cuts69176 = true := by
 decide +kernel
def pointBounds69176 : List (Nat × Nat × Nat) := [(9071071232,115668622325569,115669011745458)]
theorem point_links_checked69176 : (cuts69176.take 1).map (fun c => (9070968833-1+2*2^10*c.k,115668485079321+c.lower,115668874499138+c.upper)) = pointBounds69176 := by
 decide +kernel
def cuts69177 : List PrefixCut := [⟨64,179568475,179568578⟩]
theorem checked69177 : checkPrefixCuts (2^48) 9071099905 10 Manual.Count131072.C069177.packed 64 cuts69177 = true := by
 decide +kernel
def cuts69178 : List PrefixCut := [⟨61,170070992,170071095⟩,
⟨64,178014408,178014515⟩]
theorem checked69178 : checkPrefixCuts (2^48) 9071230977 10 Manual.Count131072.C069178.packed 64 cuts69178 = true := by
 decide +kernel
def pointBounds69178 : List (Nat × Nat × Nat) := [(9071355904,115669011186832,115669400606950)]
theorem point_links_checked69178 : (cuts69178.take 1).map (fun c => (9071230977-1+2*2^10*c.k,115668841115840+c.lower,115669230535855+c.upper)) = pointBounds69178 := by
 decide +kernel
def cuts69179 : List PrefixCut := [⟨64,178166981,178167086⟩]
theorem checked69179 : checkPrefixCuts (2^48) 9071362049 10 Manual.Count131072.C069179.packed 64 cuts69179 = true := by
 decide +kernel
def cuts69180 : List PrefixCut := [⟨64,178878047,178878155⟩]
theorem checked69180 : checkPrefixCuts (2^48) 9071493121 10 Manual.Count131072.C069180.packed 64 cuts69180 = true := by
 decide +kernel
def cuts69181 : List PrefixCut := [⟨8,22278126,22278140⟩,
⟨64,177603337,177603441⟩]
theorem checked69181 : checkPrefixCuts (2^48) 9071624193 10 Manual.Count131072.C069181.packed 64 cuts69181 = true := by
 decide +kernel
def pointBounds69181 : List (Nat × Nat × Nat) := [(9071640576,115669398453402,115669787873751)]
theorem point_links_checked69181 : (cuts69181.take 1).map (fun c => (9071624193-1+2*2^10*c.k,115669376175276+c.lower,115669765595611+c.upper)) = pointBounds69181 := by
 decide +kernel
def cuts69182 : List PrefixCut := [⟨64,180393224,180393329⟩]
theorem checked69182 : checkPrefixCuts (2^48) 9071755265 10 Manual.Count131072.C069182.packed 64 cuts69182 = true := by
 decide +kernel
def cuts69183 : List PrefixCut := [⟨19,52311686,52311718⟩,
⟨64,177567168,177567271⟩]
theorem checked69183 : checkPrefixCuts (2^48) 9071886337 10 Manual.Count131072.C069183.packed 64 cuts69183 = true := by
 decide +kernel
def pointBounds69183 : List (Nat × Nat × Nat) := [(9071925248,115669786483523,115670175904099)]
theorem point_links_checked69183 : (cuts69183.take 1).map (fun c => (9071886337-1+2*2^10*c.k,115669734171837+c.lower,115670123592381+c.upper)) = pointBounds69183 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000286
