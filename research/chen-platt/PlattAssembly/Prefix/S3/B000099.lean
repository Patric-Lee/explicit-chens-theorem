import PlattAssemblyKernel
import PlattCertificates.Count131072.C023168
import PlattCertificates.Count131072.C023169
import PlattCertificates.Count131072.C023170
import PlattCertificates.Count131072.C023171
import PlattCertificates.Count131072.C023172
import PlattCertificates.Count131072.C023173
import PlattCertificates.Count131072.C023174
import PlattCertificates.Count131072.C023175
import PlattCertificates.Count131072.C023176
import PlattCertificates.Count131072.C023177
import PlattCertificates.Count131072.C023178
import PlattCertificates.Count131072.C023179
import PlattCertificates.Count131072.C023180
import PlattCertificates.Count131072.C023181
import PlattCertificates.Count131072.C023182
import PlattCertificates.Count131072.C023183
import PlattCertificates.Count131072.C023184
import PlattCertificates.Count131072.C023185
import PlattCertificates.Count131072.C023186
import PlattCertificates.Count131072.C023187
import PlattCertificates.Count131072.C023188
import PlattCertificates.Count131072.C023189
import PlattCertificates.Count131072.C023190
import PlattCertificates.Count131072.C023191
import PlattCertificates.Count131072.C023192
import PlattCertificates.Count131072.C023193
import PlattCertificates.Count131072.C023194
import PlattCertificates.Count131072.C023195
import PlattCertificates.Count131072.C023196
import PlattCertificates.Count131072.C023197
import PlattCertificates.Count131072.C023198
import PlattCertificates.Count131072.C023199
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000099
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23168 : List PrefixCut := [⟨48,210969652,210969768⟩,
⟨128,562917628,562917942⟩]
theorem checked23168 : checkPrefixCuts (2^48) 3040608257 9 Manual.Count131072.C023168.packed 128 cuts23168 = true := by
 decide +kernel
def pointBounds23168 : List (Nat × Nat × Nat) := [(3040657408,101920132412631,101920513877352)]
theorem point_links_checked23168 : (cuts23168.take 1).map (fun c => (3040608257-1+2*2^9*c.k,101919921442979+c.lower,101920302907584+c.upper)) = pointBounds23168 := by
 decide +kernel
def cuts23169 : List PrefixCut := [⟨13,58132521,58132556⟩,
⟨106,457740206,457740464⟩,
⟨128,552988841,552989152⟩]
theorem checked23169 : checkPrefixCuts (2^48) 3040739329 9 Manual.Count131072.C023169.packed 128 cuts23169 = true := by
 decide +kernel
def pointBounds23169 : List (Nat × Nat × Nat) := [(3040752640,101920542493128,101920923958082),(3040847872,101920942100813,101921323565990)]
theorem point_links_checked23169 : (cuts23169.take 2).map (fun c => (3040739329-1+2*2^9*c.k,101920484360607+c.lower,101920865825526+c.upper)) = pointBounds23169 := by
 decide +kernel
def cuts23170 : List PrefixCut := [⟨71,306938268,306938449⟩,
⟨128,556297117,556297446⟩]
theorem checked23170 : checkPrefixCuts (2^48) 3040870401 9 Manual.Count131072.C023170.packed 128 cuts23170 = true := by
 decide +kernel
def pointBounds23170 : List (Nat × Nat × Nat) := [(3040943104,101921344287716,101921725753127)]
theorem point_links_checked23170 : (cuts23170.take 1).map (fun c => (3040870401-1+2*2^9*c.k,101921037349448+c.lower,101921418814678+c.upper)) = pointBounds23170 := by
 decide +kernel
def cuts23171 : List PrefixCut := [⟨36,153926234,153926321⟩,
⟨128,552941041,552941355⟩]
theorem checked23171 : checkPrefixCuts (2^48) 3041001473 9 Manual.Count131072.C023171.packed 128 cuts23171 = true := by
 decide +kernel
def pointBounds23171 : List (Nat × Nat × Nat) := [(3041038336,101921747572799,101922129038445)]
theorem point_links_checked23171 : (cuts23171.take 1).map (fun c => (3041001473-1+2*2^9*c.k,101921593646565+c.lower,101921975112124+c.upper)) = pointBounds23171 := by
 decide +kernel
def cuts23172 : List PrefixCut := [⟨1,4905464,4905467⟩,
⟨94,408535442,408535672⟩,
⟨128,555971550,555971864⟩]
theorem checked23172 : checkPrefixCuts (2^48) 3041132545 9 Manual.Count131072.C023172.packed 128 cuts23172 = true := by
 decide +kernel
def pointBounds23172 : List (Nat × Nat × Nat) := [(3041133568,101922151493070,101922532958946),(3041228800,101922555123048,101922936589151)]
theorem point_links_checked23172 : (cuts23172.take 2).map (fun c => (3041132545-1+2*2^9*c.k,101922146587606+c.lower,101922528053479+c.upper)) = pointBounds23172 := by
 decide +kernel
def cuts23173 : List PrefixCut := [⟨59,258402532,258402672⟩,
⟨128,560297517,560297830⟩]
theorem checked23173 : checkPrefixCuts (2^48) 3041263617 9 Manual.Count131072.C023173.packed 128 cuts23173 = true := by
 decide +kernel
def pointBounds23173 : List (Nat × Nat × Nat) := [(3041324032,101922960961688,101923342428015)]
theorem point_links_checked23173 : (cuts23173.take 1).map (fun c => (3041263617-1+2*2^9*c.k,101922702559156+c.lower,101923084025343+c.upper)) = pointBounds23173 := by
 decide +kernel
def cuts23174 : List PrefixCut := [⟨24,104301132,104301192⟩,
⟨117,508633594,508633891⟩,
⟨128,557959627,557959953⟩]
theorem checked23174 : checkPrefixCuts (2^48) 3041394689 9 Manual.Count131072.C023174.packed 128 cuts23174 = true := by
 decide +kernel
def pointBounds23174 : List (Nat × Nat × Nat) := [(3041419264,101923367157805,101923748624365),(3041514496,101923771490267,101924152957064)]
theorem point_links_checked23174 : (cuts23174.take 2).map (fun c => (3041394689-1+2*2^9*c.k,101923262856673+c.lower,101923644323173+c.upper)) = pointBounds23174 := by
 decide +kernel
def cuts23175 : List PrefixCut := [⟨82,355178889,355179086⟩,
⟨128,552568219,552568528⟩]
theorem checked23175 : checkPrefixCuts (2^48) 3041525761 9 Manual.Count131072.C023175.packed 128 cuts23175 = true := by
 decide +kernel
def pointBounds23175 : List (Nat × Nat × Nat) := [(3041609728,101924175995189,101924557462212)]
theorem point_links_checked23175 : (cuts23175.take 1).map (fun c => (3041525761-1+2*2^9*c.k,101923820816300+c.lower,101924202283126+c.upper)) = pointBounds23175 := by
 decide +kernel
def cuts23176 : List PrefixCut := [⟨47,204974482,204974599⟩,
⟨128,557911599,557911915⟩]
theorem checked23176 : checkPrefixCuts (2^48) 3041656833 9 Manual.Count131072.C023176.packed 128 cuts23176 = true := by
 decide +kernel
def pointBounds23176 : List (Nat × Nat × Nat) := [(3041704960,101924578359001,101924959826253)]
theorem point_links_checked23176 : (cuts23176.take 1).map (fun c => (3041656833-1+2*2^9*c.k,101924373384519+c.lower,101924754851654+c.upper)) = pointBounds23176 := by
 decide +kernel
def cuts23177 : List PrefixCut := [⟨12,52375272,52375302⟩,
⟨105,458230262,458230522⟩,
⟨128,558627894,558628210⟩]
theorem checked23177 : checkPrefixCuts (2^48) 3041787905 9 Manual.Count131072.C023177.packed 128 cuts23177 = true := by
 decide +kernel
def pointBounds23177 : List (Nat × Nat × Nat) := [(3041800192,101924983671390,101925365138871),(3041895424,101925389526380,101925770994091)]
theorem point_links_checked23177 : (cuts23177.take 2).map (fun c => (3041787905-1+2*2^9*c.k,101924931296118+c.lower,101925312763569+c.upper)) = pointBounds23177 := by
 decide +kernel
def cuts23178 : List PrefixCut := [⟨70,301003122,301003299⟩,
⟨128,549905975,549906288⟩]
theorem checked23178 : checkPrefixCuts (2^48) 3041918977 9 Manual.Count131072.C023178.packed 128 cuts23178 = true := by
 decide +kernel
def pointBounds23178 : List (Nat × Nat × Nat) := [(3041990656,101925790927134,101926172395078)]
theorem point_links_checked23178 : (cuts23178.take 1).map (fun c => (3041918977-1+2*2^9*c.k,101925489924012+c.lower,101925871391779+c.upper)) = pointBounds23178 := by
 decide +kernel
def cuts23179 : List PrefixCut := [⟨35,151837601,151837687⟩,
⟨128,552195386,552195696⟩]
theorem checked23179 : checkPrefixCuts (2^48) 3042050049 9 Manual.Count131072.C023179.packed 128 cuts23179 = true := by
 decide +kernel
def pointBounds23179 : List (Nat × Nat × Nat) := [(3042085888,101926191667588,101926573135754),(3042181120,101926592025373,101926973493763)]
theorem point_links_checked23179 : (cuts23179.take 2).map (fun c => (3042050049-1+2*2^9*c.k,101926039829987+c.lower,101926421298067+c.upper)) = pointBounds23179 := by
 decide +kernel
def cuts23180 : List PrefixCut := [⟨93,404138699,404138924⟩,
⟨128,555964997,555965310⟩]
theorem checked23180 : checkPrefixCuts (2^48) 3042181121 9 Manual.Count131072.C023180.packed 128 cuts23180 = true := by
 decide +kernel
def pointBounds23180 : List (Nat × Nat × Nat) := [(3042276352,101926996164072,101927377632687)]
theorem point_links_checked23180 : (cuts23180.take 1).map (fun c => (3042181121-1+2*2^9*c.k,101926592025373+c.lower,101926973493763+c.upper)) = pointBounds23180 := by
 decide +kernel
def cuts23181 : List PrefixCut := [⟨58,248228905,248229050⟩,
⟨128,552332827,552333153⟩]
theorem checked23181 : checkPrefixCuts (2^48) 3042312193 9 Manual.Count131072.C023181.packed 128 cuts23181 = true := by
 decide +kernel
def pointBounds23181 : List (Nat × Nat × Nat) := [(3042371584,101927396219275,101927777688123)]
theorem point_links_checked23181 : (cuts23181.take 1).map (fun c => (3042312193-1+2*2^9*c.k,101927147990370+c.lower,101927529459073+c.upper)) = pointBounds23181 := by
 decide +kernel
def cuts23182 : List PrefixCut := [⟨23,99916962,99917021⟩,
⟨116,508550858,508551154⟩,
⟨128,559802653,559802980⟩]
theorem checked23182 : checkPrefixCuts (2^48) 3042443265 9 Manual.Count131072.C023182.packed 128 cuts23182 = true := by
 decide +kernel
def pointBounds23182 : List (Nat × Nat × Nat) := [(3042466816,101927800240159,101928181709247),(3042562048,101928208874055,101928590343380)]
theorem point_links_checked23182 : (cuts23182.take 2).map (fun c => (3042443265-1+2*2^9*c.k,101927700323197+c.lower,101928081792226+c.upper)) = pointBounds23182 := by
 decide +kernel
def cuts23183 : List PrefixCut := [⟨81,348765810,348766005⟩,
⟨128,553395341,553395653⟩]
theorem checked23183 : checkPrefixCuts (2^48) 3042574337 9 Manual.Count131072.C023183.packed 128 cuts23183 = true := by
 decide +kernel
def pointBounds23183 : List (Nat × Nat × Nat) := [(3042657280,101928608891660,101928990361211)]
theorem point_links_checked23183 : (cuts23183.take 1).map (fun c => (3042574337-1+2*2^9*c.k,101928260125850+c.lower,101928641595206+c.upper)) = pointBounds23183 := by
 decide +kernel
def cuts23184 : List PrefixCut := [⟨46,198890903,198891018⟩,
⟨128,559846913,559847236⟩]
theorem checked23184 : checkPrefixCuts (2^48) 3042705409 9 Manual.Count131072.C023184.packed 128 cuts23184 = true := by
 decide +kernel
def pointBounds23184 : List (Nat × Nat × Nat) := [(3042752512,101929012412094,101929393881877)]
theorem point_links_checked23184 : (cuts23184.take 1).map (fun c => (3042705409-1+2*2^9*c.k,101928813521191+c.lower,101929194990859+c.upper)) = pointBounds23184 := by
 decide +kernel
def cuts23185 : List PrefixCut := [⟨11,48194558,48194586⟩,
⟨104,463622544,463622795⟩,
⟨128,565003093,565003404⟩]
theorem checked23185 : checkPrefixCuts (2^48) 3042836481 9 Manual.Count131072.C023185.packed 128 cuts23185 = true := by
 decide +kernel
def pointBounds23185 : List (Nat × Nat × Nat) := [(3042847744,101929421562662,101929803032681),(3042942976,101929836990648,101930218460890)]
theorem point_links_checked23185 : (cuts23185.take 2).map (fun c => (3042836481-1+2*2^9*c.k,101929373368104+c.lower,101929754838095+c.upper)) = pointBounds23185 := by
 decide +kernel
def cuts23186 : List PrefixCut := [⟨69,300066949,300067116⟩,
⟨128,551936482,551936798⟩]
theorem checked23186 : checkPrefixCuts (2^48) 3042967553 9 Manual.Count131072.C023186.packed 128 cuts23186 = true := by
 decide +kernel
def pointBounds23186 : List (Nat × Nat × Nat) := [(3043038208,101930238438146,101930619908615)]
theorem point_links_checked23186 : (cuts23186.take 1).map (fun c => (3042967553-1+2*2^9*c.k,101929938371197+c.lower,101930319841499+c.upper)) = pointBounds23186 := by
 decide +kernel
def cuts23187 : List PrefixCut := [⟨34,146698052,146698136⟩,
⟨127,552837663,552837973⟩,
⟨128,558109717,558110030⟩]
theorem checked23187 : checkPrefixCuts (2^48) 3043098625 9 Manual.Count131072.C023187.packed 128 cuts23187 = true := by
 decide +kernel
def pointBounds23187 : List (Nat × Nat × Nat) := [(3043133440,101930637005731,101931018476433),(3043228672,101931043145342,101931424616270)]
theorem point_links_checked23187 : (cuts23187.take 2).map (fun c => (3043098625-1+2*2^9*c.k,101930490307679+c.lower,101930871778297+c.upper)) = pointBounds23187 := by
 decide +kernel
def cuts23188 : List PrefixCut := [⟨92,401317303,401317535⟩,
⟨128,554108711,554109032⟩]
theorem checked23188 : checkPrefixCuts (2^48) 3043229697 9 Manual.Count131072.C023188.packed 128 cuts23188 = true := by
 decide +kernel
def pointBounds23188 : List (Nat × Nat × Nat) := [(3043323904,101931449734699,101931831205862)]
theorem point_links_checked23188 : (cuts23188.take 1).map (fun c => (3043229697-1+2*2^9*c.k,101931048417396+c.lower,101931429888327+c.upper)) = pointBounds23188 := by
 decide +kernel
def cuts23189 : List PrefixCut := [⟨57,246108673,246108818⟩,
⟨128,550662754,550663073⟩]
theorem checked23189 : checkPrefixCuts (2^48) 3043360769 9 Manual.Count131072.C023189.packed 128 cuts23189 = true := by
 decide +kernel
def pointBounds23189 : List (Nat × Nat × Nat) := [(3043419136,101931848634780,101932230106177)]
theorem point_links_checked23189 : (cuts23189.take 1).map (fun c => (3043360769-1+2*2^9*c.k,101931602526107+c.lower,101931983997359+c.upper)) = pointBounds23189 := by
 decide +kernel
def cuts23190 : List PrefixCut := [⟨22,93408695,93408747⟩,
⟨115,503566667,503566950⟩,
⟨128,561274447,561274761⟩]
theorem checked23190 : checkPrefixCuts (2^48) 3043491841 9 Manual.Count131072.C023190.packed 128 cuts23190 = true := by
 decide +kernel
def pointBounds23190 : List (Nat × Nat × Nat) := [(3043514368,101932246597556,101932628069179),(3043609600,101932656755528,101933038227382)]
theorem point_links_checked23190 : (cuts23190.take 2).map (fun c => (3043491841-1+2*2^9*c.k,101932153188861+c.lower,101932534660432+c.upper)) = pointBounds23190 := by
 decide +kernel
def cuts23191 : List PrefixCut := [⟨80,344484173,344484366⟩,
⟨128,545806528,545806842⟩]
theorem checked23191 : checkPrefixCuts (2^48) 3043622913 9 Manual.Count131072.C023191.packed 128 cuts23191 = true := by
 decide +kernel
def pointBounds23191 : List (Nat × Nat × Nat) := [(3043704832,101933058947481,101933440419559)]
theorem point_links_checked23191 : (cuts23191.take 1).map (fun c => (3043622913-1+2*2^9*c.k,101932714463308+c.lower,101933095935193+c.upper)) = pointBounds23191 := by
 decide +kernel
def cuts23192 : List PrefixCut := [⟨45,196233089,196233199⟩,
⟨128,555215380,555215692⟩]
theorem checked23192 : checkPrefixCuts (2^48) 3043753985 9 Manual.Count131072.C023192.packed 128 cuts23192 = true := by
 decide +kernel
def pointBounds23192 : List (Nat × Nat × Nat) := [(3043800064,101933456502925,101933837975234)]
theorem point_links_checked23192 : (cuts23192.take 1).map (fun c => (3043753985-1+2*2^9*c.k,101933260269836+c.lower,101933641742035+c.upper)) = pointBounds23192 := by
 decide +kernel
def cuts23193 : List PrefixCut := [⟨10,44294134,44294159⟩,
⟨103,452828785,452829042⟩,
⟨128,560092432,560092750⟩]
theorem checked23193 : checkPrefixCuts (2^48) 3043885057 9 Manual.Count131072.C023193.packed 128 cuts23193 = true := by
 decide +kernel
def pointBounds23193 : List (Nat × Nat × Nat) := [(3043895296,101933859779350,101934241251886),(3043990528,101934268314001,101934649786769)]
theorem point_links_checked23193 : (cuts23193.take 2).map (fun c => (3043885057-1+2*2^9*c.k,101933815485216+c.lower,101934196957727+c.upper)) = pointBounds23193 := by
 decide +kernel
def cuts23194 : List PrefixCut := [⟨68,299408845,299409011⟩,
⟨128,563027184,563027495⟩]
theorem checked23194 : checkPrefixCuts (2^48) 3044016129 9 Manual.Count131072.C023194.packed 128 cuts23194 = true := by
 decide +kernel
def pointBounds23194 : List (Nat × Nat × Nat) := [(3044085760,101934674986493,101935056459488)]
theorem point_links_checked23194 : (cuts23194.take 1).map (fun c => (3044016129-1+2*2^9*c.k,101934375577648+c.lower,101934757050477+c.upper)) = pointBounds23194 := by
 decide +kernel
def cuts23195 : List PrefixCut := [⟨33,141839419,141839503⟩,
⟨126,545527746,545528060⟩,
⟨128,553849176,553849495⟩]
theorem checked23195 : checkPrefixCuts (2^48) 3044147201 9 Manual.Count131072.C023195.packed 128 cuts23195 = true := by
 decide +kernel
def pointBounds23195 : List (Nat × Nat × Nat) := [(3044180992,101935080444251,101935461917475),(3044276224,101935484132578,101935865606032)]
theorem point_links_checked23195 : (cuts23195.take 2).map (fun c => (3044147201-1+2*2^9*c.k,101934938604832+c.lower,101935320077972+c.upper)) = pointBounds23195 := by
 decide +kernel
def cuts23196 : List PrefixCut := [⟨91,390453884,390454107⟩,
⟨128,550866602,550866917⟩]
theorem checked23196 : checkPrefixCuts (2^48) 3044278273 9 Manual.Count131072.C023196.packed 128 cuts23196 = true := by
 decide +kernel
def pointBounds23196 : List (Nat × Nat × Nat) := [(3044371456,101935882907892,101936264381574)]
theorem point_links_checked23196 : (cuts23196.take 1).map (fun c => (3044278273-1+2*2^9*c.k,101935492454008+c.lower,101935873927467+c.upper)) = pointBounds23196 := by
 decide +kernel
def cuts23197 : List PrefixCut := [⟨56,248890091,248890231⟩,
⟨128,559348776,559349090⟩]
theorem checked23197 : checkPrefixCuts (2^48) 3044409345 9 Manual.Count131072.C023197.packed 128 cuts23197 = true := by
 decide +kernel
def pointBounds23197 : List (Nat × Nat × Nat) := [(3044466688,101936292210701,101936673684615)]
theorem point_links_checked23197 : (cuts23197.take 1).map (fun c => (3044409345-1+2*2^9*c.k,101936043320610+c.lower,101936424794384+c.upper)) = pointBounds23197 := by
 decide +kernel
def cuts23198 : List PrefixCut := [⟨21,91157694,91157745⟩,
⟨114,494333243,494333531⟩,
⟨128,553962575,553962898⟩]
theorem checked23198 : checkPrefixCuts (2^48) 3044540417 9 Manual.Count131072.C023198.packed 128 cuts23198 = true := by
 decide +kernel
def pointBounds23198 : List (Nat × Nat × Nat) := [(3044561920,101936693827080,101937075301219),(3044657152,101937097002629,101937478477005)]
theorem point_links_checked23198 : (cuts23198.take 2).map (fun c => (3044540417-1+2*2^9*c.k,101936602669386+c.lower,101936984143474+c.upper)) = pointBounds23198 := by
 decide +kernel
def cuts23199 : List PrefixCut := [⟨79,340667719,340667912⟩,
⟨128,549963538,549963851⟩]
theorem checked23199 : checkPrefixCuts (2^48) 3044671489 9 Manual.Count131072.C023199.packed 128 cuts23199 = true := by
 decide +kernel
def pointBounds23199 : List (Nat × Nat × Nat) := [(3044752384,101937497299680,101937878774284)]
theorem point_links_checked23199 : (cuts23199.take 1).map (fun c => (3044671489-1+2*2^9*c.k,101937156631961+c.lower,101937538106372+c.upper)) = pointBounds23199 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000099
