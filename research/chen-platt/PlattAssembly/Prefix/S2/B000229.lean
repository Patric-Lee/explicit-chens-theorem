import PlattAssemblyKernel
import PlattCertificates.Count131072.C017328
import PlattCertificates.Count131072.C017329
import PlattCertificates.Count131072.C017330
import PlattCertificates.Count131072.C017331
import PlattCertificates.Count131072.C017332
import PlattCertificates.Count131072.C017333
import PlattCertificates.Count131072.C017334
import PlattCertificates.Count131072.C017335
import PlattCertificates.Count131072.C017336
import PlattCertificates.Count131072.C017337
import PlattCertificates.Count131072.C017338
import PlattCertificates.Count131072.C017339
import PlattCertificates.Count131072.C017340
import PlattCertificates.Count131072.C017341
import PlattCertificates.Count131072.C017342
import PlattCertificates.Count131072.C017343
import PlattCertificates.Count131072.C017344
import PlattCertificates.Count131072.C017345
import PlattCertificates.Count131072.C017346
import PlattCertificates.Count131072.C017347
import PlattCertificates.Count131072.C017348
import PlattCertificates.Count131072.C017349
import PlattCertificates.Count131072.C017350
import PlattCertificates.Count131072.C017351
import PlattCertificates.Count131072.C017352
import PlattCertificates.Count131072.C017353
import PlattCertificates.Count131072.C017354
import PlattCertificates.Count131072.C017355
import PlattCertificates.Count131072.C017356
import PlattCertificates.Count131072.C017357
import PlattCertificates.Count131072.C017358
import PlattCertificates.Count131072.C017359
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000229
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17328 : List PrefixCut := [⟨62,364713159,364713392⟩,
⟨128,753787097,753787570⟩]
theorem checked17328 : checkPrefixCuts (2^48) 2275147777 9 Manual.Count131072.C017328.packed 128 cuts17328 = true := by
 decide +kernel
def pointBounds17328 : List (Nat × Nat × Nat) := [(2275211264,98156932915962,98157312161732)]
theorem point_links_checked17328 : (cuts17328.take 1).map (fun c => (2275147777-1+2*2^9*c.k,98156568202803+c.lower,98156947448340+c.upper)) = pointBounds17328 := by
 decide +kernel
def cuts17329 : List PrefixCut := [⟨4,23010052,23010066⟩,
⟨74,430627635,430627900⟩,
⟨128,746568754,746569221⟩]
theorem checked17329 : checkPrefixCuts (2^48) 2275278849 9 Manual.Count131072.C017329.packed 128 cuts17329 = true := by
 decide +kernel
def pointBounds17329 : List (Nat × Nat × Nat) := [(2275282944,98157344999952,98157724245976),(2275354624,98157752617535,98158131863810)]
theorem point_links_checked17329 : (cuts17329.take 2).map (fun c => (2275278849-1+2*2^9*c.k,98157321989900+c.lower,98157701235910+c.upper)) = pointBounds17329 := by
 decide +kernel
def cuts17330 : List PrefixCut := [⟨16,94137603,94137661⟩,
⟨86,506182644,506182954⟩,
⟨128,750607911,750608372⟩]
theorem checked17330 : checkPrefixCuts (2^48) 2275409921 9 Manual.Count131072.C017330.packed 128 cuts17330 = true := by
 decide +kernel
def pointBounds17330 : List (Nat × Nat × Nat) := [(2275426304,98158162696257,98158541942792),(2275497984,98158574741298,98158953988085)]
theorem point_links_checked17330 : (cuts17330.take 2).map (fun c => (2275409921-1+2*2^9*c.k,98158068558654+c.lower,98158447805131+c.upper)) = pointBounds17330 := by
 decide +kernel
def cuts17331 : List PrefixCut := [⟨28,164143307,164143410⟩,
⟨98,578636203,578636566⟩,
⟨128,751801523,751801994⟩]
theorem checked17331 : checkPrefixCuts (2^48) 2275540993 9 Manual.Count131072.C017331.packed 128 cuts17331 = true := by
 decide +kernel
def pointBounds17331 : List (Nat × Nat × Nat) := [(2275569664,98158983309872,98159362556913),(2275641344,98159397802768,98159777050069)]
theorem point_links_checked17331 : (cuts17331.take 2).map (fun c => (2275540993-1+2*2^9*c.k,98158819166565+c.lower,98159198413503+c.upper)) = pointBounds17331 := by
 decide +kernel
def cuts17332 : List PrefixCut := [⟨40,232903725,232903874⟩,
⟨110,644154704,644155106⟩,
⟨128,751139698,751140166⟩]
theorem checked17332 : checkPrefixCuts (2^48) 2275672065 9 Manual.Count131072.C017332.packed 128 cuts17332 = true := by
 decide +kernel
def pointBounds17332 : List (Nat × Nat × Nat) := [(2275713024,98159803871813,98160183119371),(2275784704,98160215122792,98160594370603)]
theorem point_links_checked17332 : (cuts17332.take 2).map (fun c => (2275672065-1+2*2^9*c.k,98159570968088+c.lower,98159950215497+c.upper)) = pointBounds17332 := by
 decide +kernel
def cuts17333 : List PrefixCut := [⟨52,307963476,307963665⟩,
⟨122,720920023,720920467⟩,
⟨128,755301565,755302029⟩]
theorem checked17333 : checkPrefixCuts (2^48) 2275803137 9 Manual.Count131072.C017333.packed 128 cuts17333 = true := by
 decide +kernel
def pointBounds17333 : List (Nat × Nat × Nat) := [(2275856384,98160630071262,98161009319328),(2275928064,98161043027809,98161422276130)]
theorem point_links_checked17333 : (cuts17333.take 2).map (fun c => (2275803137-1+2*2^9*c.k,98160322107786+c.lower,98160701355663+c.upper)) = pointBounds17333 := by
 decide +kernel
def cuts17334 : List PrefixCut := [⟨64,380169811,380170048⟩,
⟨128,761317932,761318401⟩]
theorem checked17334 : checkPrefixCuts (2^48) 2275934209 9 Manual.Count131072.C017334.packed 128 cuts17334 = true := by
 decide +kernel
def pointBounds17334 : List (Nat × Nat × Nat) := [(2275999744,98161457579162,98161836827740)]
theorem point_links_checked17334 : (cuts17334.take 1).map (fun c => (2275934209-1+2*2^9*c.k,98161077409351+c.lower,98161456657692+c.upper)) = pointBounds17334 := by
 decide +kernel
def cuts17335 : List PrefixCut := [⟨6,37594815,37594837⟩,
⟨76,452367381,452367654⟩,
⟨128,762139786,762140250⟩]
theorem checked17335 : checkPrefixCuts (2^48) 2276065281 9 Manual.Count131072.C017335.packed 128 cuts17335 = true := by
 decide +kernel
def pointBounds17335 : List (Nat × Nat × Nat) := [(2276071424,98161876322098,98162255570930),(2276143104,98162291094664,98162670343747)]
theorem point_links_checked17335 : (cuts17335.take 2).map (fun c => (2276065281-1+2*2^9*c.k,98161838727283+c.lower,98162217976093+c.upper)) = pointBounds17335 := by
 decide +kernel
def cuts17336 : List PrefixCut := [⟨18,105976363,105976428⟩,
⟨88,512932378,512932692⟩,
⟨128,746762452,746762912⟩]
theorem checked17336 : checkPrefixCuts (2^48) 2276196353 9 Manual.Count131072.C017336.packed 128 cuts17336 = true := by
 decide +kernel
def pointBounds17336 : List (Nat × Nat × Nat) := [(2276214784,98162706843432,98163086092771),(2276286464,98163113799447,98163493049035)]
theorem point_links_checked17336 : (cuts17336.take 2).map (fun c => (2276196353-1+2*2^9*c.k,98162600867069+c.lower,98162980116343+c.upper)) = pointBounds17336 := by
 decide +kernel
def cuts17337 : List PrefixCut := [⟨30,175338902,175339013⟩,
⟨100,588575370,588575736⟩,
⟨128,749192463,749192928⟩]
theorem checked17337 : checkPrefixCuts (2^48) 2276327425 9 Manual.Count131072.C017337.packed 128 cuts17337 = true := by
 decide +kernel
def pointBounds17337 : List (Nat × Nat × Nat) := [(2276358144,98163522968423,98163902218268),(2276429824,98163936204891,98164315454991)]
theorem point_links_checked17337 : (cuts17337.take 2).map (fun c => (2276327425-1+2*2^9*c.k,98163347629521+c.lower,98163726879255+c.upper)) = pointBounds17337 := by
 decide +kernel
def cuts17338 : List PrefixCut := [⟨42,244816682,244816828⟩,
⟨112,658398067,658398467⟩,
⟨128,751869356,751869815⟩]
theorem checked17338 : checkPrefixCuts (2^48) 2276458497 9 Manual.Count131072.C017338.packed 128 cuts17338 = true := by
 decide +kernel
def pointBounds17338 : List (Nat × Nat × Nat) := [(2276501504,98164341638666,98164720889011),(2276573184,98164755220051,98165134470650)]
theorem point_links_checked17338 : (cuts17338.take 2).map (fun c => (2276458497-1+2*2^9*c.k,98164096821984+c.lower,98164476072183+c.upper)) = pointBounds17338 := by
 decide +kernel
def cuts17339 : List PrefixCut := [⟨54,313297065,313297264⟩,
⟨124,730561411,730561873⟩,
⟨128,756400465,756400941⟩]
theorem checked17339 : checkPrefixCuts (2^48) 2276589569 9 Manual.Count131072.C017339.packed 128 cuts17339 = true := by
 decide +kernel
def pointBounds17339 : List (Nat × Nat × Nat) := [(2276644864,98165161988405,98165541239262),(2276716544,98165579252751,98165958503871)]
theorem point_links_checked17339 : (cuts17339.take 2).map (fun c => (2276589569-1+2*2^9*c.k,98164848691340+c.lower,98165227941998+c.upper)) = pointBounds17339 := by
 decide +kernel
def cuts17340 : List PrefixCut := [⟨66,390670508,390670744⟩,
⟨128,752030222,752030687⟩]
theorem checked17340 : checkPrefixCuts (2^48) 2276720641 9 Manual.Count131072.C017340.packed 128 cuts17340 = true := by
 decide +kernel
def pointBounds17340 : List (Nat × Nat × Nat) := [(2276788224,98165995762313,98166375013683)]
theorem point_links_checked17340 : (cuts17340.take 1).map (fun c => (2276720641-1+2*2^9*c.k,98165605091805+c.lower,98165984342939+c.upper)) = pointBounds17340 := by
 decide +kernel
def cuts17341 : List PrefixCut := [⟨8,47595385,47595414⟩,
⟨78,458392109,458392393⟩,
⟨128,752481387,752481854⟩]
theorem checked17341 : checkPrefixCuts (2^48) 2276851713 9 Manual.Count131072.C017341.packed 128 cuts17341 = true := by
 decide +kernel
def pointBounds17341 : List (Nat × Nat × Nat) := [(2276859904,98166404717412,98166783969040),(2276931584,98166815514136,98167194766019)]
theorem point_links_checked17341 : (cuts17341.take 2).map (fun c => (2276851713-1+2*2^9*c.k,98166357122027+c.lower,98166736373626+c.upper)) = pointBounds17341 := by
 decide +kernel
def cuts17342 : List PrefixCut := [⟨20,118672253,118672326⟩,
⟨90,527341500,527341832⟩,
⟨128,750460141,750460611⟩]
theorem checked17342 : checkPrefixCuts (2^48) 2276982785 9 Manual.Count131072.C017342.packed 128 cuts17342 = true := by
 decide +kernel
def pointBounds17342 : List (Nat × Nat × Nat) := [(2277003264,98167228275667,98167607527806),(2277074944,98167636944914,98168016197312)]
theorem point_links_checked17342 : (cuts17342.take 2).map (fun c => (2276982785-1+2*2^9*c.k,98167109603414+c.lower,98167488855480+c.upper)) = pointBounds17342 := by
 decide +kernel
def cuts17343 : List PrefixCut := [⟨32,187391968,187392081⟩,
⟨102,598754905,598755273⟩,
⟨128,752518234,752518697⟩]
theorem checked17343 : checkPrefixCuts (2^48) 2277113857 9 Manual.Count131072.C017343.packed 128 cuts17343 = true := by
 decide +kernel
def pointBounds17343 : List (Nat × Nat × Nat) := [(2277146624,98168047455523,98168426708172),(2277218304,98168458818460,98168838071364)]
theorem point_links_checked17343 : (cuts17343.take 2).map (fun c => (2277113857-1+2*2^9*c.k,98167860063555+c.lower,98168239316091+c.upper)) = pointBounds17343 := by
 decide +kernel
def cuts17344 : List PrefixCut := [⟨44,257339458,257339619⟩,
⟨114,667440491,667440901⟩,
⟨128,750002971,750003431⟩]
theorem checked17344 : checkPrefixCuts (2^48) 2277244929 9 Manual.Count131072.C017344.packed 128 cuts17344 = true := by
 decide +kernel
def pointBounds17344 : List (Nat × Nat × Nat) := [(2277289984,98168869921247,98169249174407),(2277361664,98169280022280,98169659275689)]
theorem point_links_checked17344 : (cuts17344.take 2).map (fun c => (2277244929-1+2*2^9*c.k,98168612581789+c.lower,98168991834788+c.upper)) = pointBounds17344 := by
 decide +kernel
def cuts17345 : List PrefixCut := [⟨56,331604321,331604529⟩,
⟨126,744892891,744893356⟩,
⟨128,755892320,755892791⟩]
theorem checked17345 : checkPrefixCuts (2^48) 2277376001 9 Manual.Count131072.C017345.packed 128 cuts17345 = true := by
 decide +kernel
def pointBounds17345 : List (Nat × Nat × Nat) := [(2277433344,98169694189081,98170073442748),(2277505024,98170107477651,98170486731575)]
theorem point_links_checked17345 : (cuts17345.take 2).map (fun c => (2277376001-1+2*2^9*c.k,98169362584760+c.lower,98169741838219+c.upper)) = pointBounds17345 := by
 decide +kernel
def cuts17346 : List PrefixCut := [⟨68,396343964,396344213⟩,
⟨128,754365664,754366140⟩]
theorem checked17346 : checkPrefixCuts (2^48) 2277507073 9 Manual.Count131072.C017346.packed 128 cuts17346 = true := by
 decide +kernel
def pointBounds17346 : List (Nat × Nat × Nat) := [(2277576704,98170514821044,98170894075223)]
theorem point_links_checked17346 : (cuts17346.take 1).map (fun c => (2277507073-1+2*2^9*c.k,98170118477080+c.lower,98170497731010+c.upper)) = pointBounds17346 := by
 decide +kernel
def cuts17347 : List PrefixCut := [⟨10,57589043,57589078⟩,
⟨80,470097149,470097442⟩,
⟨128,753827971,753828435⟩]
theorem checked17347 : checkPrefixCuts (2^48) 2277638145 9 Manual.Count131072.C017347.packed 128 cuts17347 = true := by
 decide +kernel
def pointBounds17347 : List (Nat × Nat × Nat) := [(2277648384,98170930431787,98171309686228),(2277720064,98171342939893,98171722194592)]
theorem point_links_checked17347 : (cuts17347.take 2).map (fun c => (2277638145-1+2*2^9*c.k,98170872842744+c.lower,98171252097150+c.upper)) = pointBounds17347 := by
 decide +kernel
def cuts17348 : List PrefixCut := [⟨22,130494355,130494436⟩,
⟨92,532720055,532720381⟩,
⟨128,745258219,745258679⟩]
theorem checked17348 : checkPrefixCuts (2^48) 2277769217 9 Manual.Count131072.C017348.packed 128 cuts17348 = true := by
 decide +kernel
def pointBounds17348 : List (Nat × Nat × Nat) := [(2277791744,98171757165070,98172136420021),(2277863424,98172159390770,98172538645966)]
theorem point_links_checked17348 : (cuts17348.take 2).map (fun c => (2277769217-1+2*2^9*c.k,98171626670715+c.lower,98172005925585+c.upper)) = pointBounds17348 := by
 decide +kernel
def cuts17349 : List PrefixCut := [⟨34,200795961,200796083⟩,
⟨104,608309524,608309899⟩,
⟨128,750157838,750158298⟩]
theorem checked17349 : checkPrefixCuts (2^48) 2277900289 9 Manual.Count131072.C017349.packed 128 cuts17349 = true := by
 decide +kernel
def pointBounds17349 : List (Nat × Nat × Nat) := [(2277935104,98172572724895,98172951980347),(2278006784,98172980238458,98173359494163)]
theorem point_links_checked17349 : (cuts17349.take 2).map (fun c => (2277900289-1+2*2^9*c.k,98172371928934+c.lower,98172751184264+c.upper)) = pointBounds17349 := by
 decide +kernel
def cuts17350 : List PrefixCut := [⟨46,269729979,269730145⟩,
⟨116,681048162,681048583⟩,
⟨128,751844501,751844965⟩]
theorem checked17350 : checkPrefixCuts (2^48) 2278031361 9 Manual.Count131072.C017350.packed 128 cuts17350 = true := by
 decide +kernel
def pointBounds17350 : List (Nat × Nat × Nat) := [(2278078464,98173391816751,98173771072707),(2278150144,98173803134934,98174182391145)]
theorem point_links_checked17350 : (cuts17350.take 2).map (fun c => (2278031361-1+2*2^9*c.k,98173122086772+c.lower,98173501342562+c.upper)) = pointBounds17350 := by
 decide +kernel
def cuts17351 : List PrefixCut := [⟨58,336308192,336308403⟩,
⟨128,747724119,747724587⟩]
theorem checked17351 : checkPrefixCuts (2^48) 2278162433 9 Manual.Count131072.C017351.packed 128 cuts17351 = true := by
 decide +kernel
def pointBounds17351 : List (Nat × Nat × Nat) := [(2278221824,98174210239465,98174589495930),(2278293504,98174621655392,98175000912114)]
theorem point_links_checked17351 : (cuts17351.take 2).map (fun c => (2278162433-1+2*2^9*c.k,98173873931273+c.lower,98174253187527+c.upper)) = pointBounds17351 := by
 decide +kernel
def cuts17352 : List PrefixCut := [⟨70,415726959,415727218⟩,
⟨128,752869998,752870469⟩]
theorem checked17352 : checkPrefixCuts (2^48) 2278293505 9 Manual.Count131072.C017352.packed 128 cuts17352 = true := by
 decide +kernel
def pointBounds17352 : List (Nat × Nat × Nat) := [(2278365184,98175037382351,98175416639332)]
theorem point_links_checked17352 : (cuts17352.take 1).map (fun c => (2278293505-1+2*2^9*c.k,98174621655392+c.lower,98175000912114+c.upper)) = pointBounds17352 := by
 decide +kernel
def cuts17353 : List PrefixCut := [⟨12,68317027,68317068⟩,
⟨82,476358658,476358952⟩,
⟨128,747638067,747638527⟩]
theorem checked17353 : checkPrefixCuts (2^48) 2278424577 9 Manual.Count131072.C017353.packed 128 cuts17353 = true := by
 decide +kernel
def pointBounds17353 : List (Nat × Nat × Nat) := [(2278436864,98175442842417,98175822099651),(2278508544,98175850884048,98176230141535)]
theorem point_links_checked17353 : (cuts17353.take 2).map (fun c => (2278424577-1+2*2^9*c.k,98175374525390+c.lower,98175753782583+c.upper)) = pointBounds17353 := by
 decide +kernel
def cuts17354 : List PrefixCut := [⟨24,137737615,137737699⟩,
⟨94,539947770,539948101⟩,
⟨128,740553980,740554434⟩]
theorem checked17354 : checkPrefixCuts (2^48) 2278555649 9 Manual.Count131072.C017354.packed 128 cuts17354 = true := by
 decide +kernel
def pointBounds17354 : List (Nat × Nat × Nat) := [(2278580224,98176259901072,98176639158809),(2278651904,98176662111227,98177041369211)]
theorem point_links_checked17354 : (cuts17354.take 2).map (fun c => (2278555649-1+2*2^9*c.k,98176122163457+c.lower,98176501421110+c.upper)) = pointBounds17354 := by
 decide +kernel
def cuts17355 : List PrefixCut := [⟨36,207520386,207520518⟩,
⟨106,614646023,614646409⟩,
⟨128,745081618,745082083⟩]
theorem checked17355 : checkPrefixCuts (2^48) 2278686721 9 Manual.Count131072.C017355.packed 128 cuts17355 = true := by
 decide +kernel
def pointBounds17355 : List (Nat × Nat × Nat) := [(2278723584,98177070237823,98177449496062),(2278795264,98177477363460,98177856621953)]
theorem point_links_checked17355 : (cuts17355.take 2).map (fun c => (2278686721-1+2*2^9*c.k,98176862717437+c.lower,98177241975544+c.upper)) = pointBounds17355 := by
 decide +kernel
def cuts17356 : List PrefixCut := [⟨48,281741372,281741543⟩,
⟨118,698598866,698599298⟩,
⟨128,755908025,755908491⟩]
theorem checked17356 : checkPrefixCuts (2^48) 2278817793 9 Manual.Count131072.C017356.packed 128 cuts17356 = true := by
 decide +kernel
def pointBounds17356 : List (Nat × Nat × Nat) := [(2278866944,98177889540427,98178268799170),(2278938624,98178306397921,98178685656925)]
theorem point_links_checked17356 : (cuts17356.take 2).map (fun c => (2278817793-1+2*2^9*c.k,98177607799055+c.lower,98177987057627+c.upper)) = pointBounds17356 := by
 decide +kernel
def cuts17357 : List PrefixCut := [⟨60,356571018,356571240⟩,
⟨128,754753105,754753576⟩]
theorem checked17357 : checkPrefixCuts (2^48) 2278948865 9 Manual.Count131072.C017357.packed 128 cuts17357 = true := by
 decide +kernel
def pointBounds17357 : List (Nat × Nat × Nat) := [(2279010304,98178720278098,98179099537358)]
theorem point_links_checked17357 : (cuts17357.take 1).map (fun c => (2278948865-1+2*2^9*c.k,98178363707080+c.lower,98178742966118+c.upper)) = pointBounds17357 := by
 decide +kernel
def cuts17358 : List PrefixCut := [⟨2,12967887,12967895⟩,
⟨72,420893886,420894149⟩,
⟨128,747917082,747917548⟩]
theorem checked17358 : checkPrefixCuts (2^48) 2279079937 9 Manual.Count131072.C017358.packed 128 cuts17358 = true := by
 decide +kernel
def pointBounds17358 : List (Nat × Nat × Nat) := [(2279081984,98179131428072,98179510687589),(2279153664,98179539354071,98179918613843)]
theorem point_links_checked17358 : (cuts17358.take 2).map (fun c => (2279079937-1+2*2^9*c.k,98179118460185+c.lower,98179497719694+c.upper)) = pointBounds17358 := by
 decide +kernel
def cuts17359 : List PrefixCut := [⟨14,84471430,84471479⟩,
⟨84,491630884,491631188⟩,
⟨128,747256748,747257215⟩]
theorem checked17359 : checkPrefixCuts (2^48) 2279211009 9 Manual.Count131072.C017359.packed 128 cuts17359 = true := by
 decide +kernel
def pointBounds17359 : List (Nat × Nat × Nat) := [(2279225344,98179950848697,98180330108721),(2279297024,98180358008151,98180737268430)]
theorem point_links_checked17359 : (cuts17359.take 2).map (fun c => (2279211009-1+2*2^9*c.k,98179866377267+c.lower,98180245637242+c.upper)) = pointBounds17359 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000229
