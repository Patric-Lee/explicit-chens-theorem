import PlattAssemblyKernel
import PlattCertificates.Count131072.C042208
import PlattCertificates.Count131072.C042209
import PlattCertificates.Count131072.C042210
import PlattCertificates.Count131072.C042211
import PlattCertificates.Count131072.C042212
import PlattCertificates.Count131072.C042213
import PlattCertificates.Count131072.C042214
import PlattCertificates.Count131072.C042215
import PlattCertificates.Count131072.C042216
import PlattCertificates.Count131072.C042217
import PlattCertificates.Count131072.C042218
import PlattCertificates.Count131072.C042219
import PlattCertificates.Count131072.C042220
import PlattCertificates.Count131072.C042221
import PlattCertificates.Count131072.C042222
import PlattCertificates.Count131072.C042223
import PlattCertificates.Count131072.C042224
import PlattCertificates.Count131072.C042225
import PlattCertificates.Count131072.C042226
import PlattCertificates.Count131072.C042227
import PlattCertificates.Count131072.C042228
import PlattCertificates.Count131072.C042229
import PlattCertificates.Count131072.C042230
import PlattCertificates.Count131072.C042231
import PlattCertificates.Count131072.C042232
import PlattCertificates.Count131072.C042233
import PlattCertificates.Count131072.C042234
import PlattCertificates.Count131072.C042235
import PlattCertificates.Count131072.C042236
import PlattCertificates.Count131072.C042237
import PlattCertificates.Count131072.C042238
import PlattCertificates.Count131072.C042239
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000069
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42208 : List PrefixCut := [⟨64,296560433,296560604⟩]
theorem checked42208 : checkPrefixCuts (2^48) 5536219137 10 Manual.Count131072.C042208.packed 64 cuts42208 = true := by
 decide +kernel
def cuts42209 : List PrefixCut := [⟨21,94716853,94716909⟩,
⟨64,295333224,295333396⟩]
theorem checked42209 : checkPrefixCuts (2^48) 5536350209 10 Manual.Count131072.C042209.packed 64 cuts42209 = true := by
 decide +kernel
def pointBounds42209 : List (Nat × Nat × Nat) := [(5536393216,109540991658671,109541377562250)]
theorem point_links_checked42209 : (cuts42209.take 1).map (fun c => (5536350209-1+2*2^10*c.k,109540896941818+c.lower,109541282845341+c.upper)) = pointBounds42209 := by
 decide +kernel
def cuts42210 : List PrefixCut := [⟨42,195325889,195326000⟩,
⟨64,301020251,301020423⟩]
theorem checked42210 : checkPrefixCuts (2^48) 5536481281 10 Manual.Count131072.C042210.packed 64 cuts42210 = true := by
 decide +kernel
def pointBounds42210 : List (Nat × Nat × Nat) := [(5536567296,109541387600931,109541773504737)]
theorem point_links_checked42210 : (cuts42210.take 1).map (fun c => (5536481281-1+2*2^10*c.k,109541192275042+c.lower,109541578178737+c.upper)) = pointBounds42210 := by
 decide +kernel
def cuts42211 : List PrefixCut := [⟨63,292777397,292777568⟩,
⟨64,298013674,298013848⟩]
theorem checked42211 : checkPrefixCuts (2^48) 5536612353 10 Manual.Count131072.C042211.packed 64 cuts42211 = true := by
 decide +kernel
def pointBounds42211 : List (Nat × Nat × Nat) := [(5536741376,109541786072690,109542171976728)]
theorem point_links_checked42211 : (cuts42211.take 1).map (fun c => (5536612353-1+2*2^10*c.k,109541493295293+c.lower,109541879199160+c.upper)) = pointBounds42211 := by
 decide +kernel
def cuts42212 : List PrefixCut := [⟨64,299226740,299226916⟩]
theorem checked42212 : checkPrefixCuts (2^48) 5536743425 10 Manual.Count131072.C042212.packed 64 cuts42212 = true := by
 decide +kernel
def cuts42213 : List PrefixCut := [⟨20,93436997,93437053⟩,
⟨64,295915332,295915509⟩]
theorem checked42213 : checkPrefixCuts (2^48) 5536874497 10 Manual.Count131072.C042213.packed 64 cuts42213 = true := by
 decide +kernel
def pointBounds42213 : List (Nat × Nat × Nat) := [(5536915456,109542183972704,109542569876977)]
theorem point_links_checked42213 : (cuts42213.take 1).map (fun c => (5536874497-1+2*2^10*c.k,109542090535707+c.lower,109542476439924+c.upper)) = pointBounds42213 := by
 decide +kernel
def cuts42214 : List PrefixCut := [⟨41,190478121,190478231⟩,
⟨64,297738348,297738520⟩]
theorem checked42214 : checkPrefixCuts (2^48) 5537005569 10 Manual.Count131072.C042214.packed 64 cuts42214 = true := by
 decide +kernel
def pointBounds42214 : List (Nat × Nat × Nat) := [(5537089536,109542576929160,109542962833664)]
theorem point_links_checked42214 : (cuts42214.take 1).map (fun c => (5537005569-1+2*2^10*c.k,109542386451039+c.lower,109542772355433+c.upper)) = pointBounds42214 := by
 decide +kernel
def cuts42215 : List PrefixCut := [⟨62,288479718,288479889⟩,
⟨64,298036290,298036467⟩]
theorem checked42215 : checkPrefixCuts (2^48) 5537136641 10 Manual.Count131072.C042215.packed 64 cuts42215 = true := by
 decide +kernel
def pointBounds42215 : List (Nat × Nat × Nat) := [(5537263616,109542972669105,109543358573842)]
theorem point_links_checked42215 : (cuts42215.take 1).map (fun c => (5537136641-1+2*2^10*c.k,109542684189387+c.lower,109543070093953+c.upper)) = pointBounds42215 := by
 decide +kernel
def cuts42216 : List PrefixCut := [⟨64,295690971,295691138⟩]
theorem checked42216 : checkPrefixCuts (2^48) 5537267713 10 Manual.Count131072.C042216.packed 64 cuts42216 = true := by
 decide +kernel
def cuts42217 : List PrefixCut := [⟨19,85396796,85396846⟩,
⟨64,295531452,295531631⟩]
theorem checked42217 : checkPrefixCuts (2^48) 5537398785 10 Manual.Count131072.C042217.packed 64 cuts42217 = true := by
 decide +kernel
def pointBounds42217 : List (Nat × Nat × Nat) := [(5537437696,109543363313444,109543749218404)]
theorem point_links_checked42217 : (cuts42217.take 1).map (fun c => (5537398785-1+2*2^10*c.k,109543277916648+c.lower,109543663821558+c.upper)) = pointBounds42217 := by
 decide +kernel
def cuts42218 : List PrefixCut := [⟨40,185224644,185224753⟩,
⟨64,296083629,296083802⟩]
theorem checked42218 : checkPrefixCuts (2^48) 5537529857 10 Manual.Count131072.C042218.packed 64 cuts42218 = true := by
 decide +kernel
def pointBounds42218 : List (Nat × Nat × Nat) := [(5537611776,109543758672744,109544144577942)]
theorem point_links_checked42218 : (cuts42218.take 1).map (fun c => (5537529857-1+2*2^10*c.k,109543573448100+c.lower,109543959353189+c.upper)) = pointBounds42218 := by
 decide +kernel
def cuts42219 : List PrefixCut := [⟨61,283522101,283522271⟩,
⟨64,296330764,296330942⟩]
theorem checked42219 : checkPrefixCuts (2^48) 5537660929 10 Manual.Count131072.C042219.packed 64 cuts42219 = true := by
 decide +kernel
def pointBounds42219 : List (Nat × Nat × Nat) := [(5537785856,109544153053830,109544538959262)]
theorem point_links_checked42219 : (cuts42219.take 1).map (fun c => (5537660929-1+2*2^10*c.k,109543869531729+c.lower,109544255436991+c.upper)) = pointBounds42219 := by
 decide +kernel
def cuts42220 : List PrefixCut := [⟨64,296476253,296476427⟩]
theorem checked42220 : checkPrefixCuts (2^48) 5537792001 10 Manual.Count131072.C042220.packed 64 cuts42220 = true := by
 decide +kernel
def cuts42221 : List PrefixCut := [⟨18,85642865,85642915⟩,
⟨64,297841508,297841679⟩]
theorem checked42221 : checkPrefixCuts (2^48) 5537923073 10 Manual.Count131072.C042221.packed 64 cuts42221 = true := by
 decide +kernel
def pointBounds42221 : List (Nat × Nat × Nat) := [(5537959936,109544547981611,109544933887275)]
theorem point_links_checked42221 : (cuts42221.take 1).map (fun c => (5537923073-1+2*2^10*c.k,109544462338746+c.lower,109544848244360+c.upper)) = pointBounds42221 := by
 decide +kernel
def cuts42222 : List PrefixCut := [⟨39,178752323,178752429⟩,
⟨64,296868753,296868927⟩]
theorem checked42222 : checkPrefixCuts (2^48) 5538054145 10 Manual.Count131072.C042222.packed 64 cuts42222 = true := by
 decide +kernel
def pointBounds42222 : List (Nat × Nat × Nat) := [(5538134016,109544938932577,109545324838468)]
theorem point_links_checked42222 : (cuts42222.take 1).map (fun c => (5538054145-1+2*2^10*c.k,109544760180254+c.lower,109545146086039+c.upper)) = pointBounds42222 := by
 decide +kernel
def cuts42223 : List PrefixCut := [⟨60,280547530,280547696⟩,
⟨64,299962002,299962179⟩]
theorem checked42223 : checkPrefixCuts (2^48) 5538185217 10 Manual.Count131072.C042223.packed 64 cuts42223 = true := by
 decide +kernel
def pointBounds42223 : List (Nat × Nat × Nat) := [(5538308096,109545337596537,109545723502662)]
theorem point_links_checked42223 : (cuts42223.take 1).map (fun c => (5538185217-1+2*2^10*c.k,109545057049007+c.lower,109545442954966+c.upper)) = pointBounds42223 := by
 decide +kernel
def cuts42224 : List PrefixCut := [⟨64,295685810,295685988⟩]
theorem checked42224 : checkPrefixCuts (2^48) 5538316289 10 Manual.Count131072.C042224.packed 64 cuts42224 = true := by
 decide +kernel
def cuts42225 : List PrefixCut := [⟨17,80552587,80552633⟩,
⟨64,298067425,298067593⟩]
theorem checked42225 : checkPrefixCuts (2^48) 5538447361 10 Manual.Count131072.C042225.packed 64 cuts42225 = true := by
 decide +kernel
def pointBounds42225 : List (Nat × Nat × Nat) := [(5538482176,109545733249406,109546119155766)]
theorem point_links_checked42225 : (cuts42225.take 1).map (fun c => (5538447361-1+2*2^10*c.k,109545652696819+c.lower,109546038603133+c.upper)) = pointBounds42225 := by
 decide +kernel
def cuts42226 : List PrefixCut := [⟨38,176499338,176499441⟩,
⟨64,297552159,297552330⟩]
theorem checked42226 : checkPrefixCuts (2^48) 5538578433 10 Manual.Count131072.C042226.packed 64 cuts42226 = true := by
 decide +kernel
def pointBounds42226 : List (Nat × Nat × Nat) := [(5538656256,109546127263582,109546513170167)]
theorem point_links_checked42226 : (cuts42226.take 1).map (fun c => (5538578433-1+2*2^10*c.k,109545950764244+c.lower,109546336670726+c.upper)) = pointBounds42226 := by
 decide +kernel
def cuts42227 : List PrefixCut := [⟨59,275134219,275134380⟩,
⟨64,299069696,299069872⟩]
theorem checked42227 : checkPrefixCuts (2^48) 5538709505 10 Manual.Count131072.C042227.packed 64 cuts42227 = true := by
 decide +kernel
def pointBounds42227 : List (Nat × Nat × Nat) := [(5538830336,109546523450622,109546909357436)]
theorem point_links_checked42227 : (cuts42227.take 1).map (fun c => (5538709505-1+2*2^10*c.k,109546248316403+c.lower,109546634223056+c.upper)) = pointBounds42227 := by
 decide +kernel
def cuts42228 : List PrefixCut := [⟨64,300434675,300434853⟩]
theorem checked42228 : checkPrefixCuts (2^48) 5538840577 10 Manual.Count131072.C042228.packed 64 cuts42228 = true := by
 decide +kernel
def cuts42229 : List PrefixCut := [⟨16,76174723,76174767⟩,
⟨64,297073719,297073893⟩]
theorem checked42229 : checkPrefixCuts (2^48) 5538971649 10 Manual.Count131072.C042229.packed 64 cuts42229 = true := by
 decide +kernel
def pointBounds42229 : List (Nat × Nat × Nat) := [(5539004416,109546923995497,109547309902548)]
theorem point_links_checked42229 : (cuts42229.take 1).map (fun c => (5538971649-1+2*2^10*c.k,109546847820774+c.lower,109547233727781+c.upper)) = pointBounds42229 := by
 decide +kernel
def cuts42230 : List PrefixCut := [⟨37,173027193,173027295⟩,
⟨64,299353339,299353519⟩]
theorem checked42230 : checkPrefixCuts (2^48) 5539102721 10 Manual.Count131072.C042230.packed 64 cuts42230 = true := by
 decide +kernel
def pointBounds42230 : List (Nat × Nat × Nat) := [(5539178496,109547317921686,109547703828969)]
theorem point_links_checked42230 : (cuts42230.take 1).map (fun c => (5539102721-1+2*2^10*c.k,109547144894493+c.lower,109547530801674+c.upper)) = pointBounds42230 := by
 decide +kernel
def cuts42231 : List PrefixCut := [⟨58,271906928,271907087⟩,
⟨64,300159302,300159478⟩]
theorem checked42231 : checkPrefixCuts (2^48) 5539233793 10 Manual.Count131072.C042231.packed 64 cuts42231 = true := by
 decide +kernel
def pointBounds42231 : List (Nat × Nat × Nat) := [(5539352576,109547716154760,109548102062280)]
theorem point_links_checked42231 : (cuts42231.take 1).map (fun c => (5539233793-1+2*2^10*c.k,109547444247832+c.lower,109547830155193+c.upper)) = pointBounds42231 := by
 decide +kernel
def cuts42232 : List PrefixCut := [⟨64,298119660,298119837⟩]
theorem checked42232 : checkPrefixCuts (2^48) 5539364865 10 Manual.Count131072.C042232.packed 64 cuts42232 = true := by
 decide +kernel
def cuts42233 : List PrefixCut := [⟨15,71645239,71645283⟩,
⟨64,298925641,298925819⟩]
theorem checked42233 : checkPrefixCuts (2^48) 5539495937 10 Manual.Count131072.C042233.packed 64 cuts42233 = true := by
 decide +kernel
def pointBounds42233 : List (Nat × Nat × Nat) := [(5539526656,109548114172033,109548500079791)]
theorem point_links_checked42233 : (cuts42233.take 1).map (fun c => (5539495937-1+2*2^10*c.k,109548042526794+c.lower,109548428434508+c.upper)) = pointBounds42233 := by
 decide +kernel
def cuts42234 : List PrefixCut := [⟨36,162137326,162137425⟩,
⟨64,295717411,295717586⟩]
theorem checked42234 : checkPrefixCuts (2^48) 5539627009 10 Manual.Count131072.C042234.packed 64 cuts42234 = true := by
 decide +kernel
def pointBounds42234 : List (Nat × Nat × Nat) := [(5539700736,109548503589761,109548889497752)]
theorem point_links_checked42234 : (cuts42234.take 1).map (fun c => (5539627009-1+2*2^10*c.k,109548341452435+c.lower,109548727360327+c.upper)) = pointBounds42234 := by
 decide +kernel
def cuts42235 : List PrefixCut := [⟨57,262532291,262532444⟩,
⟨64,294338615,294338788⟩]
theorem checked42235 : checkPrefixCuts (2^48) 5539758081 10 Manual.Count131072.C042235.packed 64 cuts42235 = true := by
 decide +kernel
def pointBounds42235 : List (Nat × Nat × Nat) := [(5539874816,109548899702137,109549285610357)]
theorem point_links_checked42235 : (cuts42235.take 1).map (fun c => (5539758081-1+2*2^10*c.k,109548637169846+c.lower,109549023077913+c.upper)) = pointBounds42235 := by
 decide +kernel
def cuts42236 : List PrefixCut := [⟨64,300276207,300276384⟩]
theorem checked42236 : checkPrefixCuts (2^48) 5539889153 10 Manual.Count131072.C042236.packed 64 cuts42236 = true := by
 decide +kernel
def cuts42237 : List PrefixCut := [⟨14,65490771,65490810⟩,
⟨64,300929609,300929781⟩]
theorem checked42237 : checkPrefixCuts (2^48) 5540020225 10 Manual.Count131072.C042237.packed 64 cuts42237 = true := by
 decide +kernel
def pointBounds42237 : List (Nat × Nat × Nat) := [(5540048896,109549297275439,109549683183895)]
theorem point_links_checked42237 : (cuts42237.take 1).map (fun c => (5540020225-1+2*2^10*c.k,109549231784668+c.lower,109549617693085+c.upper)) = pointBounds42237 := by
 decide +kernel
def cuts42238 : List PrefixCut := [⟨35,161207517,161207614⟩,
⟨64,295841889,295842065⟩]
theorem checked42238 : checkPrefixCuts (2^48) 5540151297 10 Manual.Count131072.C042238.packed 64 cuts42238 = true := by
 decide +kernel
def pointBounds42238 : List (Nat × Nat × Nat) := [(5540222976,109549693921794,109550079830480)]
theorem point_links_checked42238 : (cuts42238.take 1).map (fun c => (5540151297-1+2*2^10*c.k,109549532714277+c.lower,109549918622866+c.upper)) = pointBounds42238 := by
 decide +kernel
def cuts42239 : List PrefixCut := [⟨56,257274641,257274799⟩,
⟨64,296596958,296597138⟩]
theorem checked42239 : checkPrefixCuts (2^48) 5540282369 10 Manual.Count131072.C042239.packed 64 cuts42239 = true := by
 decide +kernel
def pointBounds42239 : List (Nat × Nat × Nat) := [(5540397056,109550085830807,109550471739730)]
theorem point_links_checked42239 : (cuts42239.take 1).map (fun c => (5540282369-1+2*2^10*c.k,109549828556166+c.lower,109550214464931+c.upper)) = pointBounds42239 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000069
