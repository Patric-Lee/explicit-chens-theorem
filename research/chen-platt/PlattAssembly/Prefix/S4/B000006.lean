import PlattAssemblyKernel
import PlattCertificates.Count131072.C030192
import PlattCertificates.Count131072.C030193
import PlattCertificates.Count131072.C030194
import PlattCertificates.Count131072.C030195
import PlattCertificates.Count131072.C030196
import PlattCertificates.Count131072.C030197
import PlattCertificates.Count131072.C030198
import PlattCertificates.Count131072.C030199
import PlattCertificates.Count131072.C030200
import PlattCertificates.Count131072.C030201
import PlattCertificates.Count131072.C030202
import PlattCertificates.Count131072.C030203
import PlattCertificates.Count131072.C030204
import PlattCertificates.Count131072.C030205
import PlattCertificates.Count131072.C030206
import PlattCertificates.Count131072.C030207
import PlattCertificates.Count131072.C030208
import PlattCertificates.Count131072.C030209
import PlattCertificates.Count131072.C030210
import PlattCertificates.Count131072.C030211
import PlattCertificates.Count131072.C030212
import PlattCertificates.Count131072.C030213
import PlattCertificates.Count131072.C030214
import PlattCertificates.Count131072.C030215
import PlattCertificates.Count131072.C030216
import PlattCertificates.Count131072.C030217
import PlattCertificates.Count131072.C030218
import PlattCertificates.Count131072.C030219
import PlattCertificates.Count131072.C030220
import PlattCertificates.Count131072.C030221
import PlattCertificates.Count131072.C030222
import PlattCertificates.Count131072.C030223
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30192 : List PrefixCut := [⟨112,373611989,373612194⟩,
⟨128,426618826,426619060⟩]
theorem checked30192 : checkPrefixCuts (2^48) 3961257985 9 Manual.Count131072.C030192.packed 128 cuts30192 = true := by
 decide +kernel
def pointBounds30192 : List (Nat × Nat × Nat) := [(3961372672,105309558245030,105309941612175)]
theorem point_links_checked30192 : (cuts30192.take 1).map (fun c => (3961257985-1+2*2^9*c.k,105309184633041+c.lower,105309567999981+c.upper)) = pointBounds30192 := by
 decide +kernel
def cuts30193 : List PrefixCut := [⟨105,344610100,344610293⟩,
⟨128,420352017,420352256⟩]
theorem checked30193 : checkPrefixCuts (2^48) 3961389057 9 Manual.Count131072.C030193.packed 128 cuts30193 = true := by
 decide +kernel
def pointBounds30193 : List (Nat × Nat × Nat) := [(3961496576,105309955861967,105310339229334)]
theorem point_links_checked30193 : (cuts30193.take 1).map (fun c => (3961389057-1+2*2^9*c.k,105309611251867+c.lower,105309994619041+c.upper)) = pointBounds30193 := by
 decide +kernel
def cuts30194 : List PrefixCut := [⟨98,324207282,324207467⟩,
⟨128,424743279,424743518⟩]
theorem checked30194 : checkPrefixCuts (2^48) 3961520129 9 Manual.Count131072.C030194.packed 128 cuts30194 = true := by
 decide +kernel
def pointBounds30194 : List (Nat × Nat × Nat) := [(3961620480,105310355811166,105310739178764)]
theorem point_links_checked30194 : (cuts30194.take 1).map (fun c => (3961520129-1+2*2^9*c.k,105310031603884+c.lower,105310414971297+c.upper)) = pointBounds30194 := by
 decide +kernel
def cuts30195 : List PrefixCut := [⟨91,297837644,297837811⟩,
⟨128,422526685,422526918⟩]
theorem checked30195 : checkPrefixCuts (2^48) 3961651201 9 Manual.Count131072.C030195.packed 128 cuts30195 = true := by
 decide +kernel
def pointBounds30195 : List (Nat × Nat × Nat) := [(3961744384,105310754184807,105311137552626)]
theorem point_links_checked30195 : (cuts30195.take 1).map (fun c => (3961651201-1+2*2^9*c.k,105310456347163+c.lower,105310839714815+c.upper)) = pointBounds30195 := by
 decide +kernel
def cuts30196 : List PrefixCut := [⟨84,280847907,280848068⟩,
⟨128,426562431,426562673⟩]
theorem checked30196 : checkPrefixCuts (2^48) 3961782273 9 Manual.Count131072.C030196.packed 128 cuts30196 = true := by
 decide +kernel
def pointBounds30196 : List (Nat × Nat × Nat) := [(3961868288,105311159721755,105311543089801)]
theorem point_links_checked30196 : (cuts30196.take 1).map (fun c => (3961782273-1+2*2^9*c.k,105310878873848+c.lower,105311262241733+c.upper)) = pointBounds30196 := by
 decide +kernel
def cuts30197 : List PrefixCut := [⟨77,253912998,253913142⟩,
⟨128,418946611,418946853⟩]
theorem checked30197 : checkPrefixCuts (2^48) 3961913345 9 Manual.Count131072.C030197.packed 128 cuts30197 = true := by
 decide +kernel
def pointBounds30197 : List (Nat × Nat × Nat) := [(3961992192,105311559349277,105311942717548)]
theorem point_links_checked30197 : (cuts30197.take 1).map (fun c => (3961913345-1+2*2^9*c.k,105311305436279+c.lower,105311688804406+c.upper)) = pointBounds30197 := by
 decide +kernel
def cuts30198 : List PrefixCut := [⟨70,226198357,226198485⟩,
⟨128,415735795,415736027⟩]
theorem checked30198 : checkPrefixCuts (2^48) 3962044417 9 Manual.Count131072.C030198.packed 128 cuts30198 = true := by
 decide +kernel
def pointBounds30198 : List (Nat × Nat × Nat) := [(3962116096,105311950581247,105312333949744)]
theorem point_links_checked30198 : (cuts30198.take 1).map (fun c => (3962044417-1+2*2^9*c.k,105311724382890+c.lower,105312107751259+c.upper)) = pointBounds30198 := by
 decide +kernel
def cuts30199 : List PrefixCut := [⟨63,206584074,206584193⟩,
⟨128,421689371,421689608⟩]
theorem checked30199 : checkPrefixCuts (2^48) 3962175489 9 Manual.Count131072.C030199.packed 128 cuts30199 = true := by
 decide +kernel
def pointBounds30199 : List (Nat × Nat × Nat) := [(3962240000,105312346702759,105312730071479)]
theorem point_links_checked30199 : (cuts30199.take 1).map (fun c => (3962175489-1+2*2^9*c.k,105312140118685+c.lower,105312523487286+c.upper)) = pointBounds30199 := by
 decide +kernel
def cuts30200 : List PrefixCut := [⟨56,185266151,185266259⟩,
⟨128,426576988,426577226⟩]
theorem checked30200 : checkPrefixCuts (2^48) 3962306561 9 Manual.Count131072.C030200.packed 128 cuts30200 = true := by
 decide +kernel
def pointBounds30200 : List (Nat × Nat × Nat) := [(3962363904,105312747074207,105313130443153)]
theorem point_links_checked30200 : (cuts30200.take 1).map (fun c => (3962306561-1+2*2^9*c.k,105312561808056+c.lower,105312945176894+c.upper)) = pointBounds30200 := by
 decide +kernel
def cuts30201 : List PrefixCut := [⟨49,159971586,159971676⟩,
⟨128,418038721,418038952⟩]
theorem checked30201 : checkPrefixCuts (2^48) 3962437633 9 Manual.Count131072.C030201.packed 128 cuts30201 = true := by
 decide +kernel
def pointBounds30201 : List (Nat × Nat × Nat) := [(3962487808,105313148356630,105313531725796)]
theorem point_links_checked30201 : (cuts30201.take 1).map (fun c => (3962437633-1+2*2^9*c.k,105312988385044+c.lower,105313371754120+c.upper)) = pointBounds30201 := by
 decide +kernel
def cuts30202 : List PrefixCut := [⟨42,135602112,135602188⟩,
⟨128,420582033,420582270⟩]
theorem checked30202 : checkPrefixCuts (2^48) 3962568705 9 Manual.Count131072.C030202.packed 128 cuts30202 = true := by
 decide +kernel
def pointBounds30202 : List (Nat × Nat × Nat) := [(3962611712,105313542025877,105313925395260)]
theorem point_links_checked30202 : (cuts30202.take 1).map (fun c => (3962568705-1+2*2^9*c.k,105313406423765+c.lower,105313789793072+c.upper)) = pointBounds30202 := by
 decide +kernel
def cuts30203 : List PrefixCut := [⟨35,114785731,114785798⟩,
⟨128,423622420,423622659⟩]
theorem checked30203 : checkPrefixCuts (2^48) 3962699777 9 Manual.Count131072.C030203.packed 128 cuts30203 = true := by
 decide +kernel
def pointBounds30203 : List (Nat × Nat × Nat) := [(3962735616,105313941791529,105314325161140)]
theorem point_links_checked30203 : (cuts30203.take 1).map (fun c => (3962699777-1+2*2^9*c.k,105313827005798+c.lower,105314210375342+c.upper)) = pointBounds30203 := by
 decide +kernel
def cuts30204 : List PrefixCut := [⟨28,90348236,90348288⟩,
⟨128,417997249,417997489⟩]
theorem checked30204 : checkPrefixCuts (2^48) 3962830849 9 Manual.Count131072.C030204.packed 128 cuts30204 = true := by
 decide +kernel
def pointBounds30204 : List (Nat × Nat × Nat) := [(3962859520,105314340976454,105314724346289)]
theorem point_links_checked30204 : (cuts30204.take 1).map (fun c => (3962830849-1+2*2^9*c.k,105314250628218+c.lower,105314633998001+c.upper)) = pointBounds30204 := by
 decide +kernel
def cuts30205 : List PrefixCut := [⟨21,71878519,71878558⟩,
⟨128,424162623,424162859⟩]
theorem checked30205 : checkPrefixCuts (2^48) 3962961921 9 Manual.Count131072.C030205.packed 128 cuts30205 = true := by
 decide +kernel
def pointBounds30205 : List (Nat × Nat × Nat) := [(3962983424,105314740503986,105315123874048)]
theorem point_links_checked30205 : (cuts30205.take 1).map (fun c => (3962961921-1+2*2^9*c.k,105314668625467+c.lower,105315051995490+c.upper)) = pointBounds30205 := by
 decide +kernel
def cuts30206 : List PrefixCut := [⟨14,43821756,43821782⟩,
⟨128,424006486,424006722⟩]
theorem checked30206 : checkPrefixCuts (2^48) 3963092993 9 Manual.Count131072.C030206.packed 128 cuts30206 = true := by
 decide +kernel
def pointBounds30206 : List (Nat × Nat × Nat) := [(3963107328,105315136609846,105315519980131)]
theorem point_links_checked30206 : (cuts30206.take 1).map (fun c => (3963092993-1+2*2^9*c.k,105315092788090+c.lower,105315476158349+c.upper)) = pointBounds30206 := by
 decide +kernel
def cuts30207 : List PrefixCut := [⟨7,22726921,22726934⟩,
⟨128,418310914,418311156⟩]
theorem checked30207 : checkPrefixCuts (2^48) 3963224065 9 Manual.Count131072.C030207.packed 128 cuts30207 = true := by
 decide +kernel
def pointBounds30207 : List (Nat × Nat × Nat) := [(3963231232,105315539521497,105315922892005),(3963355136,105315935105490,105316318476227)]
theorem point_links_checked30207 : (cuts30207.take 2).map (fun c => (3963224065-1+2*2^9*c.k,105315516794576+c.lower,105315900165071+c.upper)) = pointBounds30207 := by
 decide +kernel
def cuts30208 : List PrefixCut := [⟨121,399974725,399974951⟩,
⟨128,421634929,421635167⟩]
theorem checked30208 : checkPrefixCuts (2^48) 3963355137 9 Manual.Count131072.C030208.packed 128 cuts30208 = true := by
 decide +kernel
def pointBounds30208 : List (Nat × Nat × Nat) := [(3963479040,105316335080215,105316718451178)]
theorem point_links_checked30208 : (cuts30208.take 1).map (fun c => (3963355137-1+2*2^9*c.k,105315935105490+c.lower,105316318476227+c.upper)) = pointBounds30208 := by
 decide +kernel
def cuts30209 : List PrefixCut := [⟨114,378231028,378231238⟩,
⟨128,424461649,424461884⟩]
theorem checked30209 : checkPrefixCuts (2^48) 3963486209 9 Manual.Count131072.C030209.packed 128 cuts30209 = true := by
 decide +kernel
def pointBounds30209 : List (Nat × Nat × Nat) := [(3963602944,105316734971447,105317118342632)]
theorem point_links_checked30209 : (cuts30209.take 1).map (fun c => (3963486209-1+2*2^9*c.k,105316356740419+c.lower,105316740111394+c.upper)) = pointBounds30209 := by
 decide +kernel
def cuts30210 : List PrefixCut := [⟨107,344984390,344984581⟩,
⟨128,415144733,415144963⟩]
theorem checked30210 : checkPrefixCuts (2^48) 3963617281 9 Manual.Count131072.C030210.packed 128 cuts30210 = true := by
 decide +kernel
def pointBounds30210 : List (Nat × Nat × Nat) := [(3963726848,105317126186458,105317509557859)]
theorem point_links_checked30210 : (cuts30210.take 1).map (fun c => (3963617281-1+2*2^9*c.k,105316781202068+c.lower,105317164573278+c.upper)) = pointBounds30210 := by
 decide +kernel
def cuts30211 : List PrefixCut := [⟨100,330629038,330629223⟩,
⟨128,427486968,427487203⟩]
theorem checked30211 : checkPrefixCuts (2^48) 3963748353 9 Manual.Count131072.C030211.packed 128 cuts30211 = true := by
 decide +kernel
def pointBounds30211 : List (Nat × Nat × Nat) := [(3963850752,105317526975839,105317910347464)]
theorem point_links_checked30211 : (cuts30211.take 1).map (fun c => (3963748353-1+2*2^9*c.k,105317196346801+c.lower,105317579718241+c.upper)) = pointBounds30211 := by
 decide +kernel
def cuts30212 : List PrefixCut := [⟨93,305268119,305268290⟩,
⟨128,417744676,417744911⟩]
theorem checked30212 : checkPrefixCuts (2^48) 3963879425 9 Manual.Count131072.C030212.packed 128 cuts30212 = true := by
 decide +kernel
def pointBounds30212 : List (Nat × Nat × Nat) := [(3963974656,105317929101888,105318312473734)]
theorem point_links_checked30212 : (cuts30212.take 1).map (fun c => (3963879425-1+2*2^9*c.k,105317623833769+c.lower,105318007205444+c.upper)) = pointBounds30212 := by
 decide +kernel
def cuts30213 : List PrefixCut := [⟨86,286157474,286157635⟩,
⟨128,425825568,425825803⟩]
theorem checked30213 : checkPrefixCuts (2^48) 3964010497 9 Manual.Count131072.C030213.packed 128 cuts30213 = true := by
 decide +kernel
def pointBounds30213 : List (Nat × Nat × Nat) := [(3964098560,105318327735919,105318711107990)]
theorem point_links_checked30213 : (cuts30213.take 1).map (fun c => (3964010497-1+2*2^9*c.k,105318041578445+c.lower,105318424950355+c.upper)) = pointBounds30213 := by
 decide +kernel
def cuts30214 : List PrefixCut := [⟨79,262716773,262716912⟩,
⟨128,424178401,424178631⟩]
theorem checked30214 : checkPrefixCuts (2^48) 3964141569 9 Manual.Count131072.C030214.packed 128 cuts30214 = true := by
 decide +kernel
def pointBounds30214 : List (Nat × Nat × Nat) := [(3964222464,105318730120786,105319113493070)]
theorem point_links_checked30214 : (cuts30214.take 1).map (fun c => (3964141569-1+2*2^9*c.k,105318467404013+c.lower,105318850776158+c.upper)) = pointBounds30214 := by
 decide +kernel
def cuts30215 : List PrefixCut := [⟨72,238567574,238567705⟩,
⟨128,419762320,419762556⟩]
theorem checked30215 : checkPrefixCuts (2^48) 3964272641 9 Manual.Count131072.C030215.packed 128 cuts30215 = true := by
 decide +kernel
def pointBounds30215 : List (Nat × Nat × Nat) := [(3964346368,105319130149988,105319513522494)]
theorem point_links_checked30215 : (cuts30215.take 1).map (fun c => (3964272641-1+2*2^9*c.k,105318891582414+c.lower,105319274954789+c.upper)) = pointBounds30215 := by
 decide +kernel
def cuts30216 : List PrefixCut := [⟨65,214987900,214988022⟩,
⟨128,420245430,420245668⟩]
theorem checked30216 : checkPrefixCuts (2^48) 3964403713 9 Manual.Count131072.C030216.packed 128 cuts30216 = true := by
 decide +kernel
def pointBounds30216 : List (Nat × Nat × Nat) := [(3964470272,105319526332634,105319909705367)]
theorem point_links_checked30216 : (cuts30216.take 1).map (fun c => (3964403713-1+2*2^9*c.k,105319311344734+c.lower,105319694717345+c.upper)) = pointBounds30216 := by
 decide +kernel
def cuts30217 : List PrefixCut := [⟨58,186439922,186440030⟩,
⟨128,417533550,417533790⟩]
theorem checked30217 : checkPrefixCuts (2^48) 3964534785 9 Manual.Count131072.C030217.packed 128 cuts30217 = true := by
 decide +kernel
def pointBounds30217 : List (Nat × Nat × Nat) := [(3964594176,105319918030086,105320301403043)]
theorem point_links_checked30217 : (cuts30217.take 1).map (fun c => (3964534785-1+2*2^9*c.k,105319731590164+c.lower,105320114963013+c.upper)) = pointBounds30217 := by
 decide +kernel
def cuts30218 : List PrefixCut := [⟨51,165206299,165206393⟩,
⟨128,421708475,421708710⟩]
theorem checked30218 : checkPrefixCuts (2^48) 3964665857 9 Manual.Count131072.C030218.packed 128 cuts30218 = true := by
 decide +kernel
def pointBounds30218 : List (Nat × Nat × Nat) := [(3964718080,105320314330013,105320697703196)]
theorem point_links_checked30218 : (cuts30218.take 1).map (fun c => (3964665857-1+2*2^9*c.k,105320149123714+c.lower,105320532496803+c.upper)) = pointBounds30218 := by
 decide +kernel
def cuts30219 : List PrefixCut := [⟨44,144400018,144400096⟩,
⟨128,418428930,418429159⟩]
theorem checked30219 : checkPrefixCuts (2^48) 3964796929 9 Manual.Count131072.C030219.packed 128 cuts30219 = true := by
 decide +kernel
def pointBounds30219 : List (Nat × Nat × Nat) := [(3964841984,105320715232207,105321098605609)]
theorem point_links_checked30219 : (cuts30219.take 1).map (fun c => (3964796929-1+2*2^9*c.k,105320570832189+c.lower,105320954205513+c.upper)) = pointBounds30219 := by
 decide +kernel
def cuts30220 : List PrefixCut := [⟨37,122459200,122459271⟩,
⟨128,420402798,420403040⟩]
theorem checked30220 : checkPrefixCuts (2^48) 3964928001 9 Manual.Count131072.C030220.packed 128 cuts30220 = true := by
 decide +kernel
def pointBounds30220 : List (Nat × Nat × Nat) := [(3964965888,105321111720319,105321495093943)]
theorem point_links_checked30220 : (cuts30220.take 1).map (fun c => (3964928001-1+2*2^9*c.k,105320989261119+c.lower,105321372634672+c.upper)) = pointBounds30220 := by
 decide +kernel
def cuts30221 : List PrefixCut := [⟨31,100164834,100164889⟩,
⟨128,420388854,420389087⟩]
theorem checked30221 : checkPrefixCuts (2^48) 3965059073 9 Manual.Count131072.C030221.packed 128 cuts30221 = true := by
 decide +kernel
def pointBounds30221 : List (Nat × Nat × Nat) := [(3965090816,105321509828751,105321893202601)]
theorem point_links_checked30221 : (cuts30221.take 1).map (fun c => (3965059073-1+2*2^9*c.k,105321409663917+c.lower,105321793037712+c.upper)) = pointBounds30221 := by
 decide +kernel
def cuts30222 : List PrefixCut := [⟨25,82698986,82699034⟩,
⟨128,419665175,419665417⟩]
theorem checked30222 : checkPrefixCuts (2^48) 3965190145 9 Manual.Count131072.C030222.packed 128 cuts30222 = true := by
 decide +kernel
def pointBounds30222 : List (Nat × Nat × Nat) := [(3965215744,105321912751757,105322296125833)]
theorem point_links_checked30222 : (cuts30222.take 1).map (fun c => (3965190145-1+2*2^9*c.k,105321830052771+c.lower,105322213426799+c.upper)) = pointBounds30222 := by
 decide +kernel
def cuts30223 : List PrefixCut := [⟨19,62962769,62962805⟩,
⟨128,427388452,427388695⟩]
theorem checked30223 : checkPrefixCuts (2^48) 3965321217 9 Manual.Count131072.C030223.packed 128 cuts30223 = true := by
 decide +kernel
def pointBounds30223 : List (Nat × Nat × Nat) := [(3965340672,105322312680715,105322696055021)]
theorem point_links_checked30223 : (cuts30223.take 1).map (fun c => (3965321217-1+2*2^9*c.k,105322249717946+c.lower,105322633092216+c.upper)) = pointBounds30223 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000006
