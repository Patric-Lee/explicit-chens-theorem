import PlattAssemblyKernel
import PlattCertificates.Count131072.C026208
import PlattCertificates.Count131072.C026209
import PlattCertificates.Count131072.C026210
import PlattCertificates.Count131072.C026211
import PlattCertificates.Count131072.C026212
import PlattCertificates.Count131072.C026213
import PlattCertificates.Count131072.C026214
import PlattCertificates.Count131072.C026215
import PlattCertificates.Count131072.C026216
import PlattCertificates.Count131072.C026217
import PlattCertificates.Count131072.C026218
import PlattCertificates.Count131072.C026219
import PlattCertificates.Count131072.C026220
import PlattCertificates.Count131072.C026221
import PlattCertificates.Count131072.C026222
import PlattCertificates.Count131072.C026223
import PlattCertificates.Count131072.C026224
import PlattCertificates.Count131072.C026225
import PlattCertificates.Count131072.C026226
import PlattCertificates.Count131072.C026227
import PlattCertificates.Count131072.C026228
import PlattCertificates.Count131072.C026229
import PlattCertificates.Count131072.C026230
import PlattCertificates.Count131072.C026231
import PlattCertificates.Count131072.C026232
import PlattCertificates.Count131072.C026233
import PlattCertificates.Count131072.C026234
import PlattCertificates.Count131072.C026235
import PlattCertificates.Count131072.C026236
import PlattCertificates.Count131072.C026237
import PlattCertificates.Count131072.C026238
import PlattCertificates.Count131072.C026239
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000194
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26208 : List PrefixCut := [⟨56,218773316,218773437⟩,
⟨128,491150294,491150574⟩]
theorem checked26208 : checkPrefixCuts (2^48) 3439067137 9 Manual.Count131072.C026208.packed 128 cuts26208 = true := by
 decide +kernel
def pointBounds26208 : List (Nat × Nat × Nat) := [(3439124480,103503037947040,103503420302569)]
theorem point_links_checked26208 : (cuts26208.take 1).map (fun c => (3439067137-1+2*2^9*c.k,103502819173724+c.lower,103503201529132+c.upper)) = pointBounds26208 := by
 decide +kernel
def cuts26209 : List PrefixCut := [⟨33,126610769,126610839⟩,
⟨128,482620020,482620286⟩]
theorem checked26209 : checkPrefixCuts (2^48) 3439198209 9 Manual.Count131072.C026209.packed 128 cuts26209 = true := by
 decide +kernel
def pointBounds26209 : List (Nat × Nat × Nat) := [(3439232000,103503436934787,103503819290545)]
theorem point_links_checked26209 : (cuts26209.take 1).map (fun c => (3439198209-1+2*2^9*c.k,103503310324018+c.lower,103503692679706+c.upper)) = pointBounds26209 := by
 decide +kernel
def cuts26210 : List PrefixCut := [⟨10,37891891,37891912⟩,
⟨115,441028494,441028743⟩,
⟨128,491030963,491031239⟩]
theorem checked26210 : checkPrefixCuts (2^48) 3439329281 9 Manual.Count131072.C026210.packed 128 cuts26210 = true := by
 decide +kernel
def pointBounds26210 : List (Nat × Nat × Nat) := [(3439339520,103503830835929,103504213191904),(3439447040,103504233972532,103504616328735)]
theorem point_links_checked26210 : (cuts26210.take 2).map (fun c => (3439329281-1+2*2^9*c.k,103503792944038+c.lower,103504175299992+c.upper)) = pointBounds26210 := by
 decide +kernel
def cuts26211 : List PrefixCut := [⟨92,353448877,353449070⟩,
⟨128,490684926,490685192⟩]
theorem checked26211 : checkPrefixCuts (2^48) 3439460353 9 Manual.Count131072.C026211.packed 128 cuts26211 = true := by
 decide +kernel
def pointBounds26211 : List (Nat × Nat × Nat) := [(3439554560,103504637423878,103505019780301)]
theorem point_links_checked26211 : (cuts26211.take 1).map (fun c => (3439460353-1+2*2^9*c.k,103504283975001+c.lower,103504666331231+c.upper)) = pointBounds26211 := by
 decide +kernel
def cuts26212 : List PrefixCut := [⟨69,265793498,265793649⟩,
⟨128,488293090,488293364⟩]
theorem checked26212 : checkPrefixCuts (2^48) 3439591425 9 Manual.Count131072.C026212.packed 128 cuts26212 = true := by
 decide +kernel
def pointBounds26212 : List (Nat × Nat × Nat) := [(3439662080,103505040453425,103505422810072)]
theorem point_links_checked26212 : (cuts26212.take 1).map (fun c => (3439591425-1+2*2^9*c.k,103504774659927+c.lower,103505157016423+c.upper)) = pointBounds26212 := by
 decide +kernel
def cuts26213 : List PrefixCut := [⟨46,178717031,178717131⟩,
⟨128,488274530,488274806⟩]
theorem checked26213 : checkPrefixCuts (2^48) 3439722497 9 Manual.Count131072.C026213.packed 128 cuts26213 = true := by
 decide +kernel
def pointBounds26213 : List (Nat × Nat × Nat) := [(3439769600,103505441670048,103505824026918)]
theorem point_links_checked26213 : (cuts26213.take 1).map (fun c => (3439722497-1+2*2^9*c.k,103505262953017+c.lower,103505645309787+c.upper)) = pointBounds26213 := by
 decide +kernel
def cuts26214 : List PrefixCut := [⟨23,88373488,88373537⟩,
⟨128,488092226,488092498⟩]
theorem checked26214 : checkPrefixCuts (2^48) 3439853569 9 Manual.Count131072.C026214.packed 128 cuts26214 = true := by
 decide +kernel
def pointBounds26214 : List (Nat × Nat × Nat) := [(3439877120,103505839601035,103506221958130),(3439984640,103506239319773,103506621677091)]
theorem point_links_checked26214 : (cuts26214.take 2).map (fun c => (3439853569-1+2*2^9*c.k,103505751227547+c.lower,103506133584593+c.upper)) = pointBounds26214 := by
 decide +kernel
def cuts26215 : List PrefixCut := [⟨105,407152175,407152399⟩,
⟨128,490364771,490365041⟩]
theorem checked26215 : checkPrefixCuts (2^48) 3439984641 9 Manual.Count131072.C026215.packed 128 cuts26215 = true := by
 decide +kernel
def pointBounds26215 : List (Nat × Nat × Nat) := [(3440092160,103506646471948,103507028829490)]
theorem point_links_checked26215 : (cuts26215.take 1).map (fun c => (3439984641-1+2*2^9*c.k,103506239319773+c.lower,103506621677091+c.upper)) = pointBounds26215 := by
 decide +kernel
def cuts26216 : List PrefixCut := [⟨82,313617444,313617616⟩,
⟨128,490673306,490673581⟩]
theorem checked26216 : checkPrefixCuts (2^48) 3440115713 9 Manual.Count131072.C026216.packed 128 cuts26216 = true := by
 decide +kernel
def pointBounds26216 : List (Nat × Nat × Nat) := [(3440199680,103507043301988,103507425659748)]
theorem point_links_checked26216 : (cuts26216.take 1).map (fun c => (3440115713-1+2*2^9*c.k,103506729684544+c.lower,103507112042132+c.upper)) = pointBounds26216 := by
 decide +kernel
def cuts26217 : List PrefixCut := [⟨59,226143618,226143745⟩,
⟨128,488363769,488364041⟩]
theorem checked26217 : checkPrefixCuts (2^48) 3440246785 9 Manual.Count131072.C026217.packed 128 cuts26217 = true := by
 decide +kernel
def pointBounds26217 : List (Nat × Nat × Nat) := [(3440307200,103507446501468,103507828859458)]
theorem point_links_checked26217 : (cuts26217.take 1).map (fun c => (3440246785-1+2*2^9*c.k,103507220357850+c.lower,103507602715713+c.upper)) = pointBounds26217 := by
 decide +kernel
def cuts26218 : List PrefixCut := [⟨36,133848806,133848882⟩,
⟨128,488263182,488263461⟩]
theorem checked26218 : checkPrefixCuts (2^48) 3440377857 9 Manual.Count131072.C026218.packed 128 cuts26218 = true := by
 decide +kernel
def pointBounds26218 : List (Nat × Nat × Nat) := [(3440414720,103507842570425,103508224928636)]
theorem point_links_checked26218 : (cuts26218.take 1).map (fun c => (3440377857-1+2*2^9*c.k,103507708721619+c.lower,103508091079754+c.upper)) = pointBounds26218 := by
 decide +kernel
def cuts26219 : List PrefixCut := [⟨13,49577974,49578002⟩,
⟨118,445704002,445704247⟩,
⟨128,483663378,483663644⟩]
theorem checked26219 : checkPrefixCuts (2^48) 3440508929 9 Manual.Count131072.C026219.packed 128 cuts26219 = true := by
 decide +kernel
def pointBounds26219 : List (Nat × Nat × Nat) := [(3440522240,103508246562775,103508628921217),(3440629760,103508642688803,103509025047462)]
theorem point_links_checked26219 : (cuts26219.take 2).map (fun c => (3440508929-1+2*2^9*c.k,103508196984801+c.lower,103508579343215+c.upper)) = pointBounds26219 := by
 decide +kernel
def cuts26220 : List PrefixCut := [⟨95,364944230,364944433⟩,
⟨128,489698630,489698906⟩]
theorem checked26220 : checkPrefixCuts (2^48) 3440640001 9 Manual.Count131072.C026220.packed 128 cuts26220 = true := by
 decide +kernel
def pointBounds26220 : List (Nat × Nat × Nat) := [(3440737280,103509045592409,103509427951292)]
theorem point_links_checked26220 : (cuts26220.take 1).map (fun c => (3440640001-1+2*2^9*c.k,103508680648179+c.lower,103509063006859+c.upper)) = pointBounds26220 := by
 decide +kernel
def cuts26221 : List PrefixCut := [⟨73,281326952,281327108⟩,
⟨128,494097372,494097648⟩]
theorem checked26221 : checkPrefixCuts (2^48) 3440771073 9 Manual.Count131072.C026221.packed 128 cuts26221 = true := by
 decide +kernel
def pointBounds26221 : List (Nat × Nat × Nat) := [(3440845824,103509451673761,103509834032873)]
theorem point_links_checked26221 : (cuts26221.take 1).map (fun c => (3440771073-1+2*2^9*c.k,103509170346809+c.lower,103509552705765+c.upper)) = pointBounds26221 := by
 decide +kernel
def cuts26222 : List PrefixCut := [⟨51,194934208,194934318⟩,
⟨128,482053815,482054087⟩]
theorem checked26222 : checkPrefixCuts (2^48) 3440902145 9 Manual.Count131072.C026222.packed 128 cuts26222 = true := by
 decide +kernel
def pointBounds26222 : List (Nat × Nat × Nat) := [(3440954368,103509859378389,103510241737731)]
theorem point_links_checked26222 : (cuts26222.take 1).map (fun c => (3440902145-1+2*2^9*c.k,103509664444181+c.lower,103510046803413+c.upper)) = pointBounds26222 := by
 decide +kernel
def cuts26223 : List PrefixCut := [⟨29,109038300,109038361⟩,
⟨128,487270490,487270770⟩]
theorem checked26223 : checkPrefixCuts (2^48) 3441033217 9 Manual.Count131072.C026223.packed 128 cuts26223 = true := by
 decide +kernel
def pointBounds26223 : List (Nat × Nat × Nat) := [(3441062912,103510255536296,103510637895861)]
theorem point_links_checked26223 : (cuts26223.take 1).map (fun c => (3441033217-1+2*2^9*c.k,103510146497996+c.lower,103510528857500+c.upper)) = pointBounds26223 := by
 decide +kernel
def cuts26224 : List PrefixCut := [⟨7,28056142,28056157⟩,
⟨113,429015021,429015260⟩,
⟨128,483898447,483898716⟩]
theorem checked26224 : checkPrefixCuts (2^48) 3441164289 9 Manual.Count131072.C026224.packed 128 cuts26224 = true := by
 decide +kernel
def pointBounds26224 : List (Nat × Nat × Nat) := [(3441171456,103510661824628,103511044184427),(3441280000,103511062783507,103511445143530)]
theorem point_links_checked26224 : (cuts26224.take 2).map (fun c => (3441164289-1+2*2^9*c.k,103510633768486+c.lower,103511016128270+c.upper)) = pointBounds26224 := by
 decide +kernel
def cuts26225 : List PrefixCut := [⟨91,342791112,342791307⟩,
⟨128,483143846,483144120⟩]
theorem checked26225 : checkPrefixCuts (2^48) 3441295361 9 Manual.Count131072.C026225.packed 128 cuts26225 = true := by
 decide +kernel
def pointBounds26225 : List (Nat × Nat × Nat) := [(3441388544,103511460458045,103511842818293)]
theorem point_links_checked26225 : (cuts26225.take 1).map (fun c => (3441295361-1+2*2^9*c.k,103511117666933+c.lower,103511500026986+c.upper)) = pointBounds26225 := by
 decide +kernel
def cuts26226 : List PrefixCut := [⟨69,264670308,264670457⟩,
⟨128,494575750,494576022⟩]
theorem checked26226 : checkPrefixCuts (2^48) 3441426433 9 Manual.Count131072.C026226.packed 128 cuts26226 = true := by
 decide +kernel
def pointBounds26226 : List (Nat × Nat × Nat) := [(3441497088,103511865481087,103512247841563)]
theorem point_links_checked26226 : (cuts26226.take 1).map (fun c => (3441426433-1+2*2^9*c.k,103511600810779+c.lower,103511983171106+c.upper)) = pointBounds26226 := by
 decide +kernel
def cuts26227 : List PrefixCut := [⟨47,176904187,176904286⟩,
⟨128,483843041,483843316⟩]
theorem checked26227 : checkPrefixCuts (2^48) 3441557505 9 Manual.Count131072.C026227.packed 128 cuts26227 = true := by
 decide +kernel
def pointBounds26227 : List (Nat × Nat × Nat) := [(3441605632,103512272290716,103512654651414)]
theorem point_links_checked26227 : (cuts26227.take 1).map (fun c => (3441557505-1+2*2^9*c.k,103512095386529+c.lower,103512477747128+c.upper)) = pointBounds26227 := by
 decide +kernel
def cuts26228 : List PrefixCut := [⟨25,95441525,95441578⟩,
⟨128,489058783,489059052⟩]
theorem checked26228 : checkPrefixCuts (2^48) 3441688577 9 Manual.Count131072.C026228.packed 128 cuts26228 = true := by
 decide +kernel
def pointBounds26228 : List (Nat × Nat × Nat) := [(3441714176,103512674671095,103513057032022)]
theorem point_links_checked26228 : (cuts26228.take 1).map (fun c => (3441688577-1+2*2^9*c.k,103512579229570+c.lower,103512961590444+c.upper)) = pointBounds26228 := by
 decide +kernel
def cuts26229 : List PrefixCut := [⟨3,11203969,11203976⟩,
⟨109,416666655,416666886⟩,
⟨128,489285483,489285755⟩]
theorem checked26229 : checkPrefixCuts (2^48) 3441819649 9 Manual.Count131072.C026229.packed 128 cuts26229 = true := by
 decide +kernel
def pointBounds26229 : List (Nat × Nat × Nat) := [(3441822720,103513079492322,103513461853472),(3441931264,103513484955008,103513867316382)]
theorem point_links_checked26229 : (cuts26229.take 2).map (fun c => (3441819649-1+2*2^9*c.k,103513068288353+c.lower,103513450649496+c.upper)) = pointBounds26229 := by
 decide +kernel
def cuts26230 : List PrefixCut := [⟨87,330132346,330132531⟩,
⟨128,485423280,485423551⟩]
theorem checked26230 : checkPrefixCuts (2^48) 3441950721 9 Manual.Count131072.C026230.packed 128 cuts26230 = true := by
 decide +kernel
def pointBounds26230 : List (Nat × Nat × Nat) := [(3442039808,103513887706182,103514270067782)]
theorem point_links_checked26230 : (cuts26230.take 1).map (fun c => (3441950721-1+2*2^9*c.k,103513557573836+c.lower,103513939935251+c.upper)) = pointBounds26230 := by
 decide +kernel
def cuts26231 : List PrefixCut := [⟨65,248919495,248919633⟩,
⟨128,486958524,486958794⟩]
theorem checked26231 : checkPrefixCuts (2^48) 3442081793 9 Manual.Count131072.C026231.packed 128 cuts26231 = true := by
 decide +kernel
def pointBounds26231 : List (Nat × Nat × Nat) := [(3442148352,103514291916611,103514674278435)]
theorem point_links_checked26231 : (cuts26231.take 1).map (fun c => (3442081793-1+2*2^9*c.k,103514042997116+c.lower,103514425358802+c.upper)) = pointBounds26231 := by
 decide +kernel
def cuts26232 : List PrefixCut := [⟨43,163296631,163296721⟩,
⟨128,484486895,484487165⟩]
theorem checked26232 : checkPrefixCuts (2^48) 3442212865 9 Manual.Count131072.C026232.packed 128 cuts26232 = true := by
 decide +kernel
def pointBounds26232 : List (Nat × Nat × Nat) := [(3442256896,103514693252271,103515075614317)]
theorem point_links_checked26232 : (cuts26232.take 1).map (fun c => (3442212865-1+2*2^9*c.k,103514529955640+c.lower,103514912317596+c.upper)) = pointBounds26232 := by
 decide +kernel
def cuts26233 : List PrefixCut := [⟨21,81277516,81277560⟩,
⟨127,494280471,494280742⟩,
⟨128,497632848,497633120⟩]
theorem checked26233 : checkPrefixCuts (2^48) 3442343937 9 Manual.Count131072.C026233.packed 128 cuts26233 = true := by
 decide +kernel
def pointBounds26233 : List (Nat × Nat × Nat) := [(3442365440,103515095720051,103515478082321),(3442473984,103515508723006,103515891085503)]
theorem point_links_checked26233 : (cuts26233.take 2).map (fun c => (3442343937-1+2*2^9*c.k,103515014442535+c.lower,103515396804761+c.upper)) = pointBounds26233 := by
 decide +kernel
def cuts26234 : List PrefixCut := [⟨105,400316549,400316774⟩,
⟨128,489192315,489192590⟩]
theorem checked26234 : checkPrefixCuts (2^48) 3442475009 9 Manual.Count131072.C026234.packed 128 cuts26234 = true := by
 decide +kernel
def pointBounds26234 : List (Nat × Nat × Nat) := [(3442582528,103515912391932,103516294754655)]
theorem point_links_checked26234 : (cuts26234.take 1).map (fun c => (3442475009-1+2*2^9*c.k,103515512075383+c.lower,103515894437881+c.upper)) = pointBounds26234 := by
 decide +kernel
def cuts26235 : List PrefixCut := [⟨83,325082313,325082489⟩,
⟨128,499066689,499066961⟩]
theorem checked26235 : checkPrefixCuts (2^48) 3442606081 9 Manual.Count131072.C026235.packed 128 cuts26235 = true := by
 decide +kernel
def pointBounds26235 : List (Nat × Nat × Nat) := [(3442691072,103516326350011,103516708712960)]
theorem point_links_checked26235 : (cuts26235.take 1).map (fun c => (3442606081-1+2*2^9*c.k,103516001267698+c.lower,103516383630471+c.upper)) = pointBounds26235 := by
 decide +kernel
def cuts26236 : List PrefixCut := [⟨61,232602362,232602492⟩,
⟨128,486211741,486212011⟩]
theorem checked26236 : checkPrefixCuts (2^48) 3442737153 9 Manual.Count131072.C026236.packed 128 cuts26236 = true := by
 decide +kernel
def pointBounds26236 : List (Nat × Nat × Nat) := [(3442799616,103516732936749,103517115299924)]
theorem point_links_checked26236 : (cuts26236.take 1).map (fun c => (3442737153-1+2*2^9*c.k,103516500334387+c.lower,103516882697432+c.upper)) = pointBounds26236 := by
 decide +kernel
def cuts26237 : List PrefixCut := [⟨39,153454997,153455080⟩,
⟨128,490362847,490363120⟩]
theorem checked26237 : checkPrefixCuts (2^48) 3442868225 9 Manual.Count131072.C026237.packed 128 cuts26237 = true := by
 decide +kernel
def pointBounds26237 : List (Nat × Nat × Nat) := [(3442908160,103517140001125,103517522364523)]
theorem point_links_checked26237 : (cuts26237.take 1).map (fun c => (3442868225-1+2*2^9*c.k,103516986546128+c.lower,103517368909443+c.upper)) = pointBounds26237 := by
 decide +kernel
def cuts26238 : List PrefixCut := [⟨17,63440023,63440059⟩,
⟨123,469416011,469416277⟩,
⟨128,487073960,487074236⟩]
theorem checked26238 : checkPrefixCuts (2^48) 3442999297 9 Manual.Count131072.C026238.packed 128 cuts26238 = true := by
 decide +kernel
def pointBounds26238 : List (Nat × Nat × Nat) := [(3443016704,103517540348998,103517922712622),(3443125248,103517946324986,103518328688840)]
theorem point_links_checked26238 : (cuts26238.take 2).map (fun c => (3442999297-1+2*2^9*c.k,103517476908975+c.lower,103517859272563+c.upper)) = pointBounds26238 := by
 decide +kernel
def cuts26239 : List PrefixCut := [⟨101,391248180,391248397⟩,
⟨128,491469910,491470185⟩]
theorem checked26239 : checkPrefixCuts (2^48) 3443130369 9 Manual.Count131072.C026239.packed 128 cuts26239 = true := by
 decide +kernel
def pointBounds26239 : List (Nat × Nat × Nat) := [(3443233792,103518355231115,103518737595196)]
theorem point_links_checked26239 : (cuts26239.take 1).map (fun c => (3443130369-1+2*2^9*c.k,103517963982935+c.lower,103518346346799+c.upper)) = pointBounds26239 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000194
