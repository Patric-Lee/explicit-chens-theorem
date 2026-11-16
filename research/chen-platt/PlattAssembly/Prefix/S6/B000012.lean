import PlattAssemblyKernel
import PlattCertificates.Count131072.C050384
import PlattCertificates.Count131072.C050385
import PlattCertificates.Count131072.C050386
import PlattCertificates.Count131072.C050387
import PlattCertificates.Count131072.C050388
import PlattCertificates.Count131072.C050389
import PlattCertificates.Count131072.C050390
import PlattCertificates.Count131072.C050391
import PlattCertificates.Count131072.C050392
import PlattCertificates.Count131072.C050393
import PlattCertificates.Count131072.C050394
import PlattCertificates.Count131072.C050395
import PlattCertificates.Count131072.C050396
import PlattCertificates.Count131072.C050397
import PlattCertificates.Count131072.C050398
import PlattCertificates.Count131072.C050399
import PlattCertificates.Count131072.C050400
import PlattCertificates.Count131072.C050401
import PlattCertificates.Count131072.C050402
import PlattCertificates.Count131072.C050403
import PlattCertificates.Count131072.C050404
import PlattCertificates.Count131072.C050405
import PlattCertificates.Count131072.C050406
import PlattCertificates.Count131072.C050407
import PlattCertificates.Count131072.C050408
import PlattCertificates.Count131072.C050409
import PlattCertificates.Count131072.C050410
import PlattCertificates.Count131072.C050411
import PlattCertificates.Count131072.C050412
import PlattCertificates.Count131072.C050413
import PlattCertificates.Count131072.C050414
import PlattCertificates.Count131072.C050415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50384 : List PrefixCut := [⟨64,245398648,245398789⟩]
theorem checked50384 : checkPrefixCuts (2^48) 6607863809 10 Manual.Count131072.C050384.packed 64 cuts50384 = true := by
 decide +kernel
def cuts50385 : List PrefixCut := [⟨16,62062382,62062417⟩,
⟨64,250590434,250590577⟩]
theorem checked50385 : checkPrefixCuts (2^48) 6607994881 10 Manual.Count131072.C050385.packed 64 cuts50385 = true := by
 decide +kernel
def pointBounds50385 : List (Nat × Nat × Nat) := [(6608027648,111752377453941,111752764630338)]
theorem point_links_checked50385 : (cuts50385.take 1).map (fun c => (6607994881-1+2*2^10*c.k,111752315391559+c.lower,111752702567921+c.upper)) = pointBounds50385 := by
 decide +kernel
def cuts50386 : List PrefixCut := [⟨53,204242619,204242734⟩,
⟨64,245942631,245942769⟩]
theorem checked50386 : checkPrefixCuts (2^48) 6608125953 10 Manual.Count131072.C050386.packed 64 cuts50386 = true := by
 decide +kernel
def pointBounds50386 : List (Nat × Nat × Nat) := [(6608234496,111752770224612,111753157401232)]
theorem point_links_checked50386 : (cuts50386.take 1).map (fun c => (6608125953-1+2*2^10*c.k,111752565981993+c.lower,111752953158498+c.upper)) = pointBounds50386 := by
 decide +kernel
def cuts50387 : List PrefixCut := [⟨64,248876758,248876901⟩]
theorem checked50387 : checkPrefixCuts (2^48) 6608257025 10 Manual.Count131072.C050387.packed 64 cuts50387 = true := by
 decide +kernel
def cuts50388 : List PrefixCut := [⟨26,98561130,98561188⟩,
⟨64,243419870,243420012⟩]
theorem checked50388 : checkPrefixCuts (2^48) 6608388097 10 Manual.Count131072.C050388.packed 64 cuts50388 = true := by
 decide +kernel
def pointBounds50388 : List (Nat × Nat × Nat) := [(6608441344,111753159362512,111753546539356)]
theorem point_links_checked50388 : (cuts50388.take 1).map (fun c => (6608388097-1+2*2^10*c.k,111753060801382+c.lower,111753447978168+c.upper)) = pointBounds50388 := by
 decide +kernel
def cuts50389 : List PrefixCut := [⟨63,247120637,247120781⟩,
⟨64,251081683,251081830⟩]
theorem checked50389 : checkPrefixCuts (2^48) 6608519169 10 Manual.Count131072.C050389.packed 64 cuts50389 = true := by
 decide +kernel
def pointBounds50389 : List (Nat × Nat × Nat) := [(6608648192,111753551341889,111753938518961)]
theorem point_links_checked50389 : (cuts50389.take 1).map (fun c => (6608519169-1+2*2^10*c.k,111753304221252+c.lower,111753691398180+c.upper)) = pointBounds50389 := by
 decide +kernel
def cuts50390 : List PrefixCut := [⟨64,242260247,242260386⟩]
theorem checked50390 : checkPrefixCuts (2^48) 6608650241 10 Manual.Count131072.C050390.packed 64 cuts50390 = true := by
 decide +kernel
def cuts50391 : List PrefixCut := [⟨36,137994205,137994281⟩,
⟨64,246940405,246940544⟩]
theorem checked50391 : checkPrefixCuts (2^48) 6608781313 10 Manual.Count131072.C050391.packed 64 cuts50391 = true := by
 decide +kernel
def pointBounds50391 : List (Nat × Nat × Nat) := [(6608855040,111753935557387,111754322734677)]
theorem point_links_checked50391 : (cuts50391.take 1).map (fun c => (6608781313-1+2*2^10*c.k,111753797563182+c.lower,111754184740396+c.upper)) = pointBounds50391 := by
 decide +kernel
def cuts50392 : List PrefixCut := [⟨64,245530070,245530210⟩]
theorem checked50392 : checkPrefixCuts (2^48) 6608912385 10 Manual.Count131072.C050392.packed 64 cuts50392 = true := by
 decide +kernel
def cuts50393 : List PrefixCut := [⟨9,34539920,34539940⟩,
⟨64,247825013,247825159⟩]
theorem checked50393 : checkPrefixCuts (2^48) 6609043457 10 Manual.Count131072.C050393.packed 64 cuts50393 = true := by
 decide +kernel
def pointBounds50393 : List (Nat × Nat × Nat) := [(6609061888,111754324573577,111754711751090)]
theorem point_links_checked50393 : (cuts50393.take 1).map (fun c => (6609043457-1+2*2^10*c.k,111754290033657+c.lower,111754677211150+c.upper)) = pointBounds50393 := by
 decide +kernel
def cuts50394 : List PrefixCut := [⟨46,180105529,180105633⟩,
⟨64,250205020,250205164⟩]
theorem checked50394 : checkPrefixCuts (2^48) 6609174529 10 Manual.Count131072.C050394.packed 64 cuts50394 = true := by
 decide +kernel
def pointBounds50394 : List (Nat × Nat × Nat) := [(6609268736,111754717964199,111755105141942)]
theorem point_links_checked50394 : (cuts50394.take 1).map (fun c => (6609174529-1+2*2^10*c.k,111754537858670+c.lower,111754925036309+c.upper)) = pointBounds50394 := by
 decide +kernel
def cuts50395 : List PrefixCut := [⟨64,244408208,244408346⟩]
theorem checked50395 : checkPrefixCuts (2^48) 6609305601 10 Manual.Count131072.C050395.packed 64 cuts50395 = true := by
 decide +kernel
def cuts50396 : List PrefixCut := [⟨19,72738076,72738117⟩,
⟨64,247426963,247427101⟩]
theorem checked50396 : checkPrefixCuts (2^48) 6609436673 10 Manual.Count131072.C050396.packed 64 cuts50396 = true := by
 decide +kernel
def pointBounds50396 : List (Nat × Nat × Nat) := [(6609475584,111755105209974,111755492387936)]
theorem point_links_checked50396 : (cuts50396.take 1).map (fun c => (6609436673-1+2*2^10*c.k,111755032471898+c.lower,111755419649819+c.upper)) = pointBounds50396 := by
 decide +kernel
def cuts50397 : List PrefixCut := [⟨56,221317399,221317527⟩,
⟨64,250743764,250743909⟩]
theorem checked50397 : checkPrefixCuts (2^48) 6609567745 10 Manual.Count131072.C050397.packed 64 cuts50397 = true := by
 decide +kernel
def pointBounds50397 : List (Nat × Nat × Nat) := [(6609682432,111755501216260,111755888394447)]
theorem point_links_checked50397 : (cuts50397.take 1).map (fun c => (6609567745-1+2*2^10*c.k,111755279898861+c.lower,111755667076920+c.upper)) = pointBounds50397 := by
 decide +kernel
def cuts50398 : List PrefixCut := [⟨64,245798949,245799090⟩]
theorem checked50398 : checkPrefixCuts (2^48) 6609698817 10 Manual.Count131072.C050398.packed 64 cuts50398 = true := by
 decide +kernel
def cuts50399 : List PrefixCut := [⟨29,110633481,110633543⟩,
⟨64,245112732,245112871⟩]
theorem checked50399 : checkPrefixCuts (2^48) 6609829889 10 Manual.Count131072.C050399.packed 64 cuts50399 = true := by
 decide +kernel
def pointBounds50399 : List (Nat × Nat × Nat) := [(6609889280,111755887075055,111756274253462)]
theorem point_links_checked50399 : (cuts50399.take 1).map (fun c => (6609829889-1+2*2^10*c.k,111755776441574+c.lower,111756163619919+c.upper)) = pointBounds50399 := by
 decide +kernel
def cuts50400 : List PrefixCut := [⟨64,248046092,248046231⟩]
theorem checked50400 : checkPrefixCuts (2^48) 6609960961 10 Manual.Count131072.C050400.packed 64 cuts50400 = true := by
 decide +kernel
def cuts50401 : List PrefixCut := [⟨2,7409370,7409374⟩,
⟨64,250383194,250383335⟩]
theorem checked50401 : checkPrefixCuts (2^48) 6610092033 10 Manual.Count131072.C050401.packed 64 cuts50401 = true := by
 decide +kernel
def pointBounds50401 : List (Nat × Nat × Nat) := [(6610096128,111756277009768,111756664188395)]
theorem point_links_checked50401 : (cuts50401.take 1).map (fun c => (6610092033-1+2*2^10*c.k,111756269600398+c.lower,111756656779021+c.upper)) = pointBounds50401 := by
 decide +kernel
def cuts50402 : List PrefixCut := [⟨39,150695932,150696018⟩,
⟨64,247440136,247440277⟩]
theorem checked50402 : checkPrefixCuts (2^48) 6610223105 10 Manual.Count131072.C050402.packed 64 cuts50402 = true := by
 decide +kernel
def pointBounds50402 : List (Nat × Nat × Nat) := [(6610302976,111756670679524,111757057858374)]
theorem point_links_checked50402 : (cuts50402.take 1).map (fun c => (6610223105-1+2*2^10*c.k,111756519983592+c.lower,111756907162356+c.upper)) = pointBounds50402 := by
 decide +kernel
def cuts50403 : List PrefixCut := [⟨64,246626176,246626312⟩]
theorem checked50403 : checkPrefixCuts (2^48) 6610354177 10 Manual.Count131072.C050403.packed 64 cuts50403 = true := by
 decide +kernel
def cuts50404 : List PrefixCut := [⟨12,45432846,45432872⟩,
⟨64,244534875,244535017⟩]
theorem checked50404 : checkPrefixCuts (2^48) 6610485249 10 Manual.Count131072.C050404.packed 64 cuts50404 = true := by
 decide +kernel
def pointBounds50404 : List (Nat × Nat × Nat) := [(6610509824,111757059482750,111757446661817)]
theorem point_links_checked50404 : (cuts50404.take 1).map (fun c => (6610485249-1+2*2^10*c.k,111757014049904+c.lower,111757401228945+c.upper)) = pointBounds50404 := by
 decide +kernel
def cuts50405 : List PrefixCut := [⟨49,191221839,191221948⟩,
⟨64,249724664,249724806⟩]
theorem checked50405 : checkPrefixCuts (2^48) 6610616321 10 Manual.Count131072.C050405.packed 64 cuts50405 = true := by
 decide +kernel
def pointBounds50405 : List (Nat × Nat × Nat) := [(6610716672,111757449806618,111757836985910)]
theorem point_links_checked50405 : (cuts50405.take 1).map (fun c => (6610616321-1+2*2^10*c.k,111757258584779+c.lower,111757645763962+c.upper)) = pointBounds50405 := by
 decide +kernel
def cuts50406 : List PrefixCut := [⟨64,246270878,246271018⟩]
theorem checked50406 : checkPrefixCuts (2^48) 6610747393 10 Manual.Count131072.C050406.packed 64 cuts50406 = true := by
 decide +kernel
def cuts50407 : List PrefixCut := [⟨22,83196217,83196264⟩,
⟨64,241965714,241965854⟩]
theorem checked50407 : checkPrefixCuts (2^48) 6610878465 10 Manual.Count131072.C050407.packed 64 cuts50407 = true := by
 decide +kernel
def pointBounds50407 : List (Nat × Nat × Nat) := [(6610923520,111757837776538,111758224956050)]
theorem point_links_checked50407 : (cuts50407.take 1).map (fun c => (6610878465-1+2*2^10*c.k,111757754580321+c.lower,111758141759786+c.upper)) = pointBounds50407 := by
 decide +kernel
def cuts50408 : List PrefixCut := [⟨59,228081246,228081374⟩,
⟨64,247368119,247368257⟩]
theorem checked50408 : checkPrefixCuts (2^48) 6611009537 10 Manual.Count131072.C050408.packed 64 cuts50408 = true := by
 decide +kernel
def pointBounds50408 : List (Nat × Nat × Nat) := [(6611130368,111758224627281,111758611807014)]
theorem point_links_checked50408 : (cuts50408.take 1).map (fun c => (6611009537-1+2*2^10*c.k,111757996546035+c.lower,111758383725640+c.upper)) = pointBounds50408 := by
 decide +kernel
def cuts50409 : List PrefixCut := [⟨64,247192896,247193039⟩]
theorem checked50409 : checkPrefixCuts (2^48) 6611140609 10 Manual.Count131072.C050409.packed 64 cuts50409 = true := by
 decide +kernel
def cuts50410 : List PrefixCut := [⟨32,122147068,122147139⟩,
⟨64,246166192,246166330⟩]
theorem checked50410 : checkPrefixCuts (2^48) 6611271681 10 Manual.Count131072.C050410.packed 64 cuts50410 = true := by
 decide +kernel
def pointBounds50410 : List (Nat × Nat × Nat) := [(6611337216,111758613254118,111759000434075)]
theorem point_links_checked50410 : (cuts50410.take 1).map (fun c => (6611271681-1+2*2^10*c.k,111758491107050+c.lower,111758878286936+c.upper)) = pointBounds50410 := by
 decide +kernel
def cuts50411 : List PrefixCut := [⟨64,245352439,245352586⟩]
theorem checked50411 : checkPrefixCuts (2^48) 6611402753 10 Manual.Count131072.C050411.packed 64 cuts50411 = true := by
 decide +kernel
def cuts50412 : List PrefixCut := [⟨5,18774817,18774827⟩,
⟨64,246922756,246922897⟩]
theorem checked50412 : checkPrefixCuts (2^48) 6611533825 10 Manual.Count131072.C050412.packed 64 cuts50412 = true := by
 decide +kernel
def pointBounds50412 : List (Nat × Nat × Nat) := [(6611544064,111759001400498,111759388580679)]
theorem point_links_checked50412 : (cuts50412.take 1).map (fun c => (6611533825-1+2*2^10*c.k,111758982625681+c.lower,111759369805852+c.upper)) = pointBounds50412 := by
 decide +kernel
def cuts50413 : List PrefixCut := [⟨42,162540622,162540714⟩,
⟨64,246194153,246194293⟩]
theorem checked50413 : checkPrefixCuts (2^48) 6611664897 10 Manual.Count131072.C050413.packed 64 cuts50413 = true := by
 decide +kernel
def pointBounds50413 : List (Nat × Nat × Nat) := [(6611750912,111759392089059,111759779269463)]
theorem point_links_checked50413 : (cuts50413.take 1).map (fun c => (6611664897-1+2*2^10*c.k,111759229548437+c.lower,111759616728749+c.upper)) = pointBounds50413 := by
 decide +kernel
def cuts50414 : List PrefixCut := [⟨64,245933825,245933970⟩]
theorem checked50414 : checkPrefixCuts (2^48) 6611795969 10 Manual.Count131072.C050414.packed 64 cuts50414 = true := by
 decide +kernel
def cuts50415 : List PrefixCut := [⟨15,59343531,59343565⟩,
⟨64,249164329,249164472⟩]
theorem checked50415 : checkPrefixCuts (2^48) 6611927041 10 Manual.Count131072.C050415.packed 64 cuts50415 = true := by
 decide +kernel
def pointBounds50415 : List (Nat × Nat × Nat) := [(6611957760,111759781019946,111760168200577)]
theorem point_links_checked50415 : (cuts50415.take 1).map (fun c => (6611927041-1+2*2^10*c.k,111759721676415+c.lower,111760108857012+c.upper)) = pointBounds50415 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000012
