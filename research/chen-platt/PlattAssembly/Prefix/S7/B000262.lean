import PlattAssemblyKernel
import PlattCertificates.Count131072.C068384
import PlattCertificates.Count131072.C068385
import PlattCertificates.Count131072.C068386
import PlattCertificates.Count131072.C068387
import PlattCertificates.Count131072.C068388
import PlattCertificates.Count131072.C068389
import PlattCertificates.Count131072.C068390
import PlattCertificates.Count131072.C068391
import PlattCertificates.Count131072.C068392
import PlattCertificates.Count131072.C068393
import PlattCertificates.Count131072.C068394
import PlattCertificates.Count131072.C068395
import PlattCertificates.Count131072.C068396
import PlattCertificates.Count131072.C068397
import PlattCertificates.Count131072.C068398
import PlattCertificates.Count131072.C068399
import PlattCertificates.Count131072.C068400
import PlattCertificates.Count131072.C068401
import PlattCertificates.Count131072.C068402
import PlattCertificates.Count131072.C068403
import PlattCertificates.Count131072.C068404
import PlattCertificates.Count131072.C068405
import PlattCertificates.Count131072.C068406
import PlattCertificates.Count131072.C068407
import PlattCertificates.Count131072.C068408
import PlattCertificates.Count131072.C068409
import PlattCertificates.Count131072.C068410
import PlattCertificates.Count131072.C068411
import PlattCertificates.Count131072.C068412
import PlattCertificates.Count131072.C068413
import PlattCertificates.Count131072.C068414
import PlattCertificates.Count131072.C068415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000262
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68384 : List PrefixCut := [⟨38,105405561,105405629⟩,
⟨64,178385356,178385469⟩]
theorem checked68384 : checkPrefixCuts (2^48) 8967159809 10 Manual.Count131072.C068384.packed 64 cuts68384 = true := by
 decide +kernel
def pointBounds68384 : List (Nat × Nat × Nat) := [(8967237632,115527241837039,115527631174031)]
theorem point_links_checked68384 : (cuts68384.take 1).map (fun c => (8967159809-1+2*2^10*c.k,115527136431478+c.lower,115527525768402+c.upper)) = pointBounds68384 := by
 decide +kernel
def cuts68385 : List PrefixCut := [⟨64,181019429,181019540⟩]
theorem checked68385 : checkPrefixCuts (2^48) 8967290881 10 Manual.Count131072.C068385.packed 64 cuts68385 = true := by
 decide +kernel
def cuts68386 : List PrefixCut := [⟨47,130983953,130984030⟩,
⟨64,179478739,179478845⟩]
theorem checked68386 : checkPrefixCuts (2^48) 8967421953 10 Manual.Count131072.C068386.packed 64 cuts68386 = true := by
 decide +kernel
def pointBounds68386 : List (Nat × Nat × Nat) := [(8967518208,115527626820216,115528016157441)]
theorem point_links_checked68386 : (cuts68386.take 1).map (fun c => (8967421953-1+2*2^10*c.k,115527495836263+c.lower,115527885173411+c.upper)) = pointBounds68386 := by
 decide +kernel
def cuts68387 : List PrefixCut := [⟨64,181516344,181516446⟩]
theorem checked68387 : checkPrefixCuts (2^48) 8967553025 10 Manual.Count131072.C068387.packed 64 cuts68387 = true := by
 decide +kernel
def cuts68388 : List PrefixCut := [⟨56,155305291,155305385⟩,
⟨64,177966895,177966999⟩]
theorem checked68388 : checkPrefixCuts (2^48) 8967684097 10 Manual.Count131072.C068388.packed 64 cuts68388 = true := by
 decide +kernel
def pointBounds68388 : List (Nat × Nat × Nat) := [(8967798784,115528012136637,115528401474087)]
theorem point_links_checked68388 : (cuts68388.take 1).map (fun c => (8967684097-1+2*2^10*c.k,115527856831346+c.lower,115528246168702+c.upper)) = pointBounds68388 := by
 decide +kernel
def cuts68389 : List PrefixCut := [⟨64,182892059,182892167⟩]
theorem checked68389 : checkPrefixCuts (2^48) 8967815169 10 Manual.Count131072.C068389.packed 64 cuts68389 = true := by
 decide +kernel
def cuts68390 : List PrefixCut := [⟨64,181822247,181822344⟩]
theorem checked68390 : checkPrefixCuts (2^48) 8967946241 10 Manual.Count131072.C068390.packed 64 cuts68390 = true := by
 decide +kernel
def cuts68391 : List PrefixCut := [⟨1,2416746,2416747⟩,
⟨64,176923359,176923462⟩]
theorem checked68391 : checkPrefixCuts (2^48) 8968077313 10 Manual.Count131072.C068391.packed 64 cuts68391 = true := by
 decide +kernel
def pointBounds68391 : List (Nat × Nat × Nat) := [(8968079360,115528401929293,115528791266959)]
theorem point_links_checked68391 : (cuts68391.take 1).map (fun c => (8968077313-1+2*2^10*c.k,115528399512547+c.lower,115528788850212+c.upper)) = pointBounds68391 := by
 decide +kernel
def cuts68392 : List PrefixCut := [⟨64,174692393,174692493⟩]
theorem checked68392 : checkPrefixCuts (2^48) 8968208385 10 Manual.Count131072.C068392.packed 64 cuts68392 = true := by
 decide +kernel
def cuts68393 : List PrefixCut := [⟨10,28152668,28152686⟩,
⟨64,179429003,179429108⟩]
theorem checked68393 : checkPrefixCuts (2^48) 8968339457 10 Manual.Count131072.C068393.packed 64 cuts68393 = true := by
 decide +kernel
def pointBounds68393 : List (Nat × Nat × Nat) := [(8968359936,115528779280967,115529168618853)]
theorem point_links_checked68393 : (cuts68393.take 1).map (fun c => (8968339457-1+2*2^10*c.k,115528751128299+c.lower,115529140466167+c.upper)) = pointBounds68393 := by
 decide +kernel
def cuts68394 : List PrefixCut := [⟨64,179991312,179991418⟩]
theorem checked68394 : checkPrefixCuts (2^48) 8968470529 10 Manual.Count131072.C068394.packed 64 cuts68394 = true := by
 decide +kernel
def cuts68395 : List PrefixCut := [⟨19,53981188,53981218⟩,
⟨64,181557895,181557994⟩]
theorem checked68395 : checkPrefixCuts (2^48) 8968601601 10 Manual.Count131072.C068395.packed 64 cuts68395 = true := by
 decide +kernel
def pointBounds68395 : List (Nat × Nat × Nat) := [(8968640512,115529164529802,115529553867911)]
theorem point_links_checked68395 : (cuts68395.take 1).map (fun c => (8968601601-1+2*2^10*c.k,115529110548614+c.lower,115529499886693+c.upper)) = pointBounds68395 := by
 decide +kernel
def cuts68396 : List PrefixCut := [⟨64,175717849,175717953⟩]
theorem checked68396 : checkPrefixCuts (2^48) 8968732673 10 Manual.Count131072.C068396.packed 64 cuts68396 = true := by
 decide +kernel
def cuts68397 : List PrefixCut := [⟨28,79713991,79714037⟩,
⟨64,180611081,180611183⟩]
theorem checked68397 : checkPrefixCuts (2^48) 8968863745 10 Manual.Count131072.C068397.packed 64 cuts68397 = true := by
 decide +kernel
def pointBounds68397 : List (Nat × Nat × Nat) := [(8968921088,115529547538349,115529936876677)]
theorem point_links_checked68397 : (cuts68397.take 1).map (fun c => (8968863745-1+2*2^10*c.k,115529467824358+c.lower,115529857162640+c.upper)) = pointBounds68397 := by
 decide +kernel
def cuts68398 : List PrefixCut := [⟨64,180263242,180263346⟩]
theorem checked68398 : checkPrefixCuts (2^48) 8968994817 10 Manual.Count131072.C068398.packed 64 cuts68398 = true := by
 decide +kernel
def cuts68399 : List PrefixCut := [⟨37,102652195,102652249⟩,
⟨64,179162204,179162305⟩]
theorem checked68399 : checkPrefixCuts (2^48) 8969125889 10 Manual.Count131072.C068399.packed 64 cuts68399 = true := by
 decide +kernel
def pointBounds68399 : List (Nat × Nat × Nat) := [(8969201664,115529931350876,115530320689418)]
theorem point_links_checked68399 : (cuts68399.take 1).map (fun c => (8969125889-1+2*2^10*c.k,115529828698681+c.lower,115530218037169+c.upper)) = pointBounds68399 := by
 decide +kernel
def cuts68400 : List PrefixCut := [⟨64,177590498,177590601⟩]
theorem checked68400 : checkPrefixCuts (2^48) 8969256961 10 Manual.Count131072.C068400.packed 64 cuts68400 = true := by
 decide +kernel
def cuts68401 : List PrefixCut := [⟨46,129417564,129417643⟩,
⟨64,180506375,180506483⟩]
theorem checked68401 : checkPrefixCuts (2^48) 8969388033 10 Manual.Count131072.C068401.packed 64 cuts68401 = true := by
 decide +kernel
def pointBounds68401 : List (Nat × Nat × Nat) := [(8969482240,115530314868947,115530704207718)]
theorem point_links_checked68401 : (cuts68401.take 1).map (fun c => (8969388033-1+2*2^10*c.k,115530185451383+c.lower,115530574790075+c.upper)) = pointBounds68401 := by
 decide +kernel
def cuts68402 : List PrefixCut := [⟨64,177648063,177648166⟩]
theorem checked68402 : checkPrefixCuts (2^48) 8969519105 10 Manual.Count131072.C068402.packed 64 cuts68402 = true := by
 decide +kernel
def cuts68403 : List PrefixCut := [⟨55,154831945,154832038⟩,
⟨64,179999013,179999121⟩]
theorem checked68403 : checkPrefixCuts (2^48) 8969650177 10 Manual.Count131072.C068403.packed 64 cuts68403 = true := by
 decide +kernel
def pointBounds68403 : List (Nat × Nat × Nat) := [(8969762816,115530698437766,115531087776762)]
theorem point_links_checked68403 : (cuts68403.take 1).map (fun c => (8969650177-1+2*2^10*c.k,115530543605821+c.lower,115530932944724+c.upper)) = pointBounds68403 := by
 decide +kernel
def cuts68404 : List PrefixCut := [⟨64,180655357,180655464⟩]
theorem checked68404 : checkPrefixCuts (2^48) 8969781249 10 Manual.Count131072.C068404.packed 64 cuts68404 = true := by
 decide +kernel
def cuts68405 : List PrefixCut := [⟨64,181625502,181625604⟩]
theorem checked68405 : checkPrefixCuts (2^48) 8969912321 10 Manual.Count131072.C068405.packed 64 cuts68405 = true := by
 decide +kernel
def pointBounds68405 : List (Nat × Nat × Nat) := [(8970043392,115531085885693,115531475224913)]
theorem point_links_checked68405 : (cuts68405.take 1).map (fun c => (8969912321-1+2*2^10*c.k,115530904260191+c.lower,115531293599309+c.upper)) = pointBounds68405 := by
 decide +kernel
def cuts68406 : List PrefixCut := [⟨64,178610431,178610535⟩]
theorem checked68406 : checkPrefixCuts (2^48) 8970043393 10 Manual.Count131072.C068406.packed 64 cuts68406 = true := by
 decide +kernel
def cuts68407 : List PrefixCut := [⟨64,180835731,180835837⟩]
theorem checked68407 : checkPrefixCuts (2^48) 8970174465 10 Manual.Count131072.C068407.packed 64 cuts68407 = true := by
 decide +kernel
def cuts68408 : List PrefixCut := [⟨9,25416574,25416588⟩,
⟨64,178605219,178605326⟩]
theorem checked68408 : checkPrefixCuts (2^48) 8970305537 10 Manual.Count131072.C068408.packed 64 cuts68408 = true := by
 decide +kernel
def pointBounds68408 : List (Nat × Nat × Nat) := [(8970323968,115531470748429,115531860087873)]
theorem point_links_checked68408 : (cuts68408.take 1).map (fun c => (8970305537-1+2*2^10*c.k,115531445331855+c.lower,115531834671285+c.upper)) = pointBounds68408 := by
 decide +kernel
def cuts68409 : List PrefixCut := [⟨64,179104659,179104767⟩]
theorem checked68409 : checkPrefixCuts (2^48) 8970436609 10 Manual.Count131072.C068409.packed 64 cuts68409 = true := by
 decide +kernel
def cuts68410 : List PrefixCut := [⟨18,51678804,51678834⟩,
⟨64,180043372,180043477⟩]
theorem checked68410 : checkPrefixCuts (2^48) 8970567681 10 Manual.Count131072.C068410.packed 64 cuts68410 = true := by
 decide +kernel
def pointBounds68410 : List (Nat × Nat × Nat) := [(8970604544,115531854720537,115532244060212)]
theorem point_links_checked68410 : (cuts68410.take 1).map (fun c => (8970567681-1+2*2^10*c.k,115531803041733+c.lower,115532192381378+c.upper)) = pointBounds68410 := by
 decide +kernel
def cuts68411 : List PrefixCut := [⟨64,178566010,178566116⟩]
theorem checked68411 : checkPrefixCuts (2^48) 8970698753 10 Manual.Count131072.C068411.packed 64 cuts68411 = true := by
 decide +kernel
def cuts68412 : List PrefixCut := [⟨27,75868591,75868634⟩,
⟨64,181387283,181387384⟩]
theorem checked68412 : checkPrefixCuts (2^48) 8970829825 10 Manual.Count131072.C068412.packed 64 cuts68412 = true := by
 decide +kernel
def pointBounds68412 : List (Nat × Nat × Nat) := [(8970885120,115532237519706,115532626859605)]
theorem point_links_checked68412 : (cuts68412.take 1).map (fun c => (8970829825-1+2*2^10*c.k,115532161651115+c.lower,115532550990971+c.upper)) = pointBounds68412 := by
 decide +kernel
def cuts68413 : List PrefixCut := [⟨64,178749040,178749149⟩]
theorem checked68413 : checkPrefixCuts (2^48) 8970960897 10 Manual.Count131072.C068413.packed 64 cuts68413 = true := by
 decide +kernel
def cuts68414 : List PrefixCut := [⟨36,102221825,102221884⟩,
⟨64,181507482,181507588⟩]
theorem checked68414 : checkPrefixCuts (2^48) 8971091969 10 Manual.Count131072.C068414.packed 64 cuts68414 = true := by
 decide +kernel
def pointBounds68414 : List (Nat × Nat × Nat) := [(8971165696,115532624009263,115533013349388)]
theorem point_links_checked68414 : (cuts68414.take 1).map (fun c => (8971091969-1+2*2^10*c.k,115532521787438+c.lower,115532911127504+c.upper)) = pointBounds68414 := by
 decide +kernel
def cuts68415 : List PrefixCut := [⟨64,178461455,178461562⟩]
theorem checked68415 : checkPrefixCuts (2^48) 8971223041 10 Manual.Count131072.C068415.packed 64 cuts68415 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000262
