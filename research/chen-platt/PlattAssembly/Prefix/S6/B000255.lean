import PlattAssemblyKernel
import PlattCertificates.Count131072.C058160
import PlattCertificates.Count131072.C058161
import PlattCertificates.Count131072.C058162
import PlattCertificates.Count131072.C058163
import PlattCertificates.Count131072.C058164
import PlattCertificates.Count131072.C058165
import PlattCertificates.Count131072.C058166
import PlattCertificates.Count131072.C058167
import PlattCertificates.Count131072.C058168
import PlattCertificates.Count131072.C058169
import PlattCertificates.Count131072.C058170
import PlattCertificates.Count131072.C058171
import PlattCertificates.Count131072.C058172
import PlattCertificates.Count131072.C058173
import PlattCertificates.Count131072.C058174
import PlattCertificates.Count131072.C058175
import PlattCertificates.Count131072.C058176
import PlattCertificates.Count131072.C058177
import PlattCertificates.Count131072.C058178
import PlattCertificates.Count131072.C058179
import PlattCertificates.Count131072.C058180
import PlattCertificates.Count131072.C058181
import PlattCertificates.Count131072.C058182
import PlattCertificates.Count131072.C058183
import PlattCertificates.Count131072.C058184
import PlattCertificates.Count131072.C058185
import PlattCertificates.Count131072.C058186
import PlattCertificates.Count131072.C058187
import PlattCertificates.Count131072.C058188
import PlattCertificates.Count131072.C058189
import PlattCertificates.Count131072.C058190
import PlattCertificates.Count131072.C058191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000255
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58160 : List PrefixCut := [⟨64,211978627,211978745⟩]
theorem checked58160 : checkPrefixCuts (2^48) 7627079681 10 Manual.Count131072.C058160.packed 64 cuts58160 = true := by
 decide +kernel
def cuts58161 : List PrefixCut := [⟨16,52108395,52108425⟩,
⟨64,210461924,210462044⟩]
theorem checked58161 : checkPrefixCuts (2^48) 7627210753 10 Manual.Count131072.C058161.packed 64 cuts58161 = true := by
 decide +kernel
def pointBounds58161 : List (Nat × Nat × Nat) := [(7627243520,113532245959149,113532634147001)]
theorem point_links_checked58161 : (cuts58161.take 1).map (fun c => (7627210753-1+2*2^10*c.k,113532193850754+c.lower,113532582038576+c.upper)) = pointBounds58161 := by
 decide +kernel
def cuts58162 : List PrefixCut := [⟨64,213595095,213595218⟩]
theorem checked58162 : checkPrefixCuts (2^48) 7627341825 10 Manual.Count131072.C058162.packed 64 cuts58162 = true := by
 decide +kernel
def cuts58163 : List PrefixCut := [⟨5,17307390,17307399⟩,
⟨64,216691220,216691344⟩]
theorem checked58163 : checkPrefixCuts (2^48) 7627472897 10 Manual.Count131072.C058163.packed 64 cuts58163 = true := by
 decide +kernel
def pointBounds58163 : List (Nat × Nat × Nat) := [(7627483136,113532635215163,113533023403237)]
theorem point_links_checked58163 : (cuts58163.take 1).map (fun c => (7627472897-1+2*2^10*c.k,113532617907773+c.lower,113533006095838+c.upper)) = pointBounds58163 := by
 decide +kernel
def cuts58164 : List PrefixCut := [⟨58,192959781,192959890⟩,
⟨64,213329427,213329548⟩]
theorem checked58164 : checkPrefixCuts (2^48) 7627603969 10 Manual.Count131072.C058164.packed 64 cuts58164 = true := by
 decide +kernel
def pointBounds58164 : List (Nat × Nat × Nat) := [(7627722752,113533027558774,113533415747072)]
theorem point_links_checked58164 : (cuts58164.take 1).map (fun c => (7627603969-1+2*2^10*c.k,113532834598993+c.lower,113533222787182+c.upper)) = pointBounds58164 := by
 decide +kernel
def cuts58165 : List PrefixCut := [⟨64,211886602,211886725⟩]
theorem checked58165 : checkPrefixCuts (2^48) 7627735041 10 Manual.Count131072.C058165.packed 64 cuts58165 = true := by
 decide +kernel
def cuts58166 : List PrefixCut := [⟨47,155609998,155610084⟩,
⟨64,210886678,210886796⟩]
theorem checked58166 : checkPrefixCuts (2^48) 7627866113 10 Manual.Count131072.C058166.packed 64 cuts58166 = true := by
 decide +kernel
def pointBounds58166 : List (Nat × Nat × Nat) := [(7627962368,113533415425020,113533803613539)]
theorem point_links_checked58166 : (cuts58166.take 1).map (fun c => (7627866113-1+2*2^10*c.k,113533259815022+c.lower,113533648003455+c.upper)) = pointBounds58166 := by
 decide +kernel
def cuts58167 : List PrefixCut := [⟨64,214277826,214277945⟩]
theorem checked58167 : checkPrefixCuts (2^48) 7627997185 10 Manual.Count131072.C058167.packed 64 cuts58167 = true := by
 decide +kernel
def cuts58168 : List PrefixCut := [⟨36,118853038,118853107⟩,
⟨64,211949486,211949606⟩]
theorem checked58168 : checkPrefixCuts (2^48) 7628128257 10 Manual.Count131072.C058168.packed 64 cuts58168 = true := by
 decide +kernel
def pointBounds58168 : List (Nat × Nat × Nat) := [(7628201984,113533803832564,113534192021303)]
theorem point_links_checked58168 : (cuts58168.take 1).map (fun c => (7628128257-1+2*2^10*c.k,113533684979526+c.lower,113534073168196+c.upper)) = pointBounds58168 := by
 decide +kernel
def cuts58169 : List PrefixCut := [⟨64,214085976,214086098⟩]
theorem checked58169 : checkPrefixCuts (2^48) 7628259329 10 Manual.Count131072.C058169.packed 64 cuts58169 = true := by
 decide +kernel
def cuts58170 : List PrefixCut := [⟨25,84275513,84275562⟩,
⟨64,211610138,211610261⟩]
theorem checked58170 : checkPrefixCuts (2^48) 7628390401 10 Manual.Count131072.C058170.packed 64 cuts58170 = true := by
 decide +kernel
def pointBounds58170 : List (Nat × Nat × Nat) := [(7628441600,113534195290501,113534583479462)]
theorem point_links_checked58170 : (cuts58170.take 1).map (fun c => (7628390401-1+2*2^10*c.k,113534111014988+c.lower,113534499203900+c.upper)) = pointBounds58170 := by
 decide +kernel
def cuts58171 : List PrefixCut := [⟨64,210056790,210056909⟩]
theorem checked58171 : checkPrefixCuts (2^48) 7628521473 10 Manual.Count131072.C058171.packed 64 cuts58171 = true := by
 decide +kernel
def cuts58172 : List PrefixCut := [⟨14,45088129,45088156⟩,
⟨64,212931117,212931241⟩]
theorem checked58172 : checkPrefixCuts (2^48) 7628652545 10 Manual.Count131072.C058172.packed 64 cuts58172 = true := by
 decide +kernel
def pointBounds58172 : List (Nat × Nat × Nat) := [(7628681216,113534577770045,113534965959226)]
theorem point_links_checked58172 : (cuts58172.take 1).map (fun c => (7628652545-1+2*2^10*c.k,113534532681916+c.lower,113534920871070+c.upper)) = pointBounds58172 := by
 decide +kernel
def cuts58173 : List PrefixCut := [⟨64,210197153,210197275⟩]
theorem checked58173 : checkPrefixCuts (2^48) 7628783617 10 Manual.Count131072.C058173.packed 64 cuts58173 = true := by
 decide +kernel
def cuts58174 : List PrefixCut := [⟨3,10183236,10183242⟩,
⟨64,214288957,214289076⟩]
theorem checked58174 : checkPrefixCuts (2^48) 7628914689 10 Manual.Count131072.C058174.packed 64 cuts58174 = true := by
 decide +kernel
def pointBounds58174 : List (Nat × Nat × Nat) := [(7628920832,113534965993422,113535354182828)]
theorem point_links_checked58174 : (cuts58174.take 1).map (fun c => (7628914689-1+2*2^10*c.k,113534955810186+c.lower,113535343999586+c.upper)) = pointBounds58174 := by
 decide +kernel
def cuts58175 : List PrefixCut := [⟨56,186651234,186651339⟩,
⟨64,213289113,213289234⟩]
theorem checked58175 : checkPrefixCuts (2^48) 7629045761 10 Manual.Count131072.C058175.packed 64 cuts58175 = true := by
 decide +kernel
def pointBounds58175 : List (Nat × Nat × Nat) := [(7629160448,113535356750377,113535744940001)]
theorem point_links_checked58175 : (cuts58175.take 1).map (fun c => (7629045761-1+2*2^10*c.k,113535170099143+c.lower,113535558288662+c.upper)) = pointBounds58175 := by
 decide +kernel
def cuts58176 : List PrefixCut := [⟨64,211772791,211772916⟩]
theorem checked58176 : checkPrefixCuts (2^48) 7629176833 10 Manual.Count131072.C058176.packed 64 cuts58176 = true := by
 decide +kernel
def cuts58177 : List PrefixCut := [⟨45,149898997,149899083⟩,
⟨64,212433238,212433361⟩]
theorem checked58177 : checkPrefixCuts (2^48) 7629307905 10 Manual.Count131072.C058177.packed 64 cuts58177 = true := by
 decide +kernel
def pointBounds58177 : List (Nat × Nat × Nat) := [(7629400064,113535745060044,113536133249895)]
theorem point_links_checked58177 : (cuts58177.take 1).map (fun c => (7629307905-1+2*2^10*c.k,113535595161047+c.lower,113535983350812+c.upper)) = pointBounds58177 := by
 decide +kernel
def cuts58178 : List PrefixCut := [⟨64,212171319,212171439⟩]
theorem checked58178 : checkPrefixCuts (2^48) 7629438977 10 Manual.Count131072.C058178.packed 64 cuts58178 = true := by
 decide +kernel
def cuts58179 : List PrefixCut := [⟨34,112669569,112669634⟩,
⟨64,211909441,211909562⟩]
theorem checked58179 : checkPrefixCuts (2^48) 7629570049 10 Manual.Count131072.C058179.packed 64 cuts58179 = true := by
 decide +kernel
def pointBounds58179 : List (Nat × Nat × Nat) := [(7629639680,113536132435173,113536520625246)]
theorem point_links_checked58179 : (cuts58179.take 1).map (fun c => (7629570049-1+2*2^10*c.k,113536019765604+c.lower,113536407955612+c.upper)) = pointBounds58179 := by
 decide +kernel
def cuts58180 : List PrefixCut := [⟨64,211167974,211168094⟩]
theorem checked58180 : checkPrefixCuts (2^48) 7629701121 10 Manual.Count131072.C058180.packed 64 cuts58180 = true := by
 decide +kernel
def cuts58181 : List PrefixCut := [⟨23,78246335,78246379⟩,
⟨64,213931181,213931300⟩]
theorem checked58181 : checkPrefixCuts (2^48) 7629832193 10 Manual.Count131072.C058181.packed 64 cuts58181 = true := by
 decide +kernel
def pointBounds58181 : List (Nat × Nat × Nat) := [(7629879296,113536521089354,113536909279647)]
theorem point_links_checked58181 : (cuts58181.take 1).map (fun c => (7629832193-1+2*2^10*c.k,113536442843019+c.lower,113536831033268+c.upper)) = pointBounds58181 := by
 decide +kernel
def cuts58182 : List PrefixCut := [⟨64,215624465,215624586⟩]
theorem checked58182 : checkPrefixCuts (2^48) 7629963265 10 Manual.Count131072.C058182.packed 64 cuts58182 = true := by
 decide +kernel
def cuts58183 : List PrefixCut := [⟨12,39730566,39730590⟩,
⟨64,210861961,210862084⟩]
theorem checked58183 : checkPrefixCuts (2^48) 7630094337 10 Manual.Count131072.C058183.packed 64 cuts58183 = true := by
 decide +kernel
def pointBounds58183 : List (Nat × Nat × Nat) := [(7630118912,113536912129231,113537300319744)]
theorem point_links_checked58183 : (cuts58183.take 1).map (fun c => (7630094337-1+2*2^10*c.k,113536872398665+c.lower,113537260589154+c.upper)) = pointBounds58183 := by
 decide +kernel
def cuts58184 : List PrefixCut := [⟨64,211965016,211965135⟩]
theorem checked58184 : checkPrefixCuts (2^48) 7630225409 10 Manual.Count131072.C058184.packed 64 cuts58184 = true := by
 decide +kernel
def cuts58185 : List PrefixCut := [⟨1,3651993,3651995⟩,
⟨64,211334284,211334402⟩]
theorem checked58185 : checkPrefixCuts (2^48) 7630356481 10 Manual.Count131072.C058185.packed 64 cuts58185 = true := by
 decide +kernel
def pointBounds58185 : List (Nat × Nat × Nat) := [(7630358528,113537298877635,113537687068368)]
theorem point_links_checked58185 : (cuts58185.take 1).map (fun c => (7630356481-1+2*2^10*c.k,113537295225642+c.lower,113537683416373+c.upper)) = pointBounds58185 := by
 decide +kernel
def cuts58186 : List PrefixCut := [⟨54,175475863,175475968⟩,
⟨64,208490274,208490398⟩]
theorem checked58186 : checkPrefixCuts (2^48) 7630487553 10 Manual.Count131072.C058186.packed 64 cuts58186 = true := by
 decide +kernel
def pointBounds58186 : List (Nat × Nat × Nat) := [(7630598144,113537682035789,113538070226743)]
theorem point_links_checked58186 : (cuts58186.take 1).map (fun c => (7630487553-1+2*2^10*c.k,113537506559926+c.lower,113537894750775+c.upper)) = pointBounds58186 := by
 decide +kernel
def cuts58187 : List PrefixCut := [⟨64,214351762,214351886⟩]
theorem checked58187 : checkPrefixCuts (2^48) 7630618625 10 Manual.Count131072.C058187.packed 64 cuts58187 = true := by
 decide +kernel
def cuts58188 : List PrefixCut := [⟨43,144153277,144153357⟩,
⟨64,215860429,215860547⟩]
theorem checked58188 : checkPrefixCuts (2^48) 7630749697 10 Manual.Count131072.C058188.packed 64 cuts58188 = true := by
 decide +kernel
def pointBounds58188 : List (Nat × Nat × Nat) := [(7630837760,113538073555239,113538461746416)]
theorem point_links_checked58188 : (cuts58188.take 1).map (fun c => (7630749697-1+2*2^10*c.k,113537929401962+c.lower,113538317593059+c.upper)) = pointBounds58188 := by
 decide +kernel
def cuts58189 : List PrefixCut := [⟨64,209217256,209217371⟩]
theorem checked58189 : checkPrefixCuts (2^48) 7630880769 10 Manual.Count131072.C058189.packed 64 cuts58189 = true := by
 decide +kernel
def cuts58190 : List PrefixCut := [⟨32,108185177,108185236⟩,
⟨64,215115324,215115441⟩]
theorem checked58190 : checkPrefixCuts (2^48) 7631011841 10 Manual.Count131072.C058190.packed 64 cuts58190 = true := by
 decide +kernel
def pointBounds58190 : List (Nat × Nat × Nat) := [(7631077376,113538462664824,113538850856213)]
theorem point_links_checked58190 : (cuts58190.take 1).map (fun c => (7631011841-1+2*2^10*c.k,113538354479647+c.lower,113538742670977+c.upper)) = pointBounds58190 := by
 decide +kernel
def cuts58191 : List PrefixCut := [⟨64,207919081,207919199⟩]
theorem checked58191 : checkPrefixCuts (2^48) 7631142913 10 Manual.Count131072.C058191.packed 64 cuts58191 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000255
