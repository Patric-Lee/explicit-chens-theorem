import PlattAssemblyKernel
import PlattCertificates.Count131072.C017392
import PlattCertificates.Count131072.C017393
import PlattCertificates.Count131072.C017394
import PlattCertificates.Count131072.C017395
import PlattCertificates.Count131072.C017396
import PlattCertificates.Count131072.C017397
import PlattCertificates.Count131072.C017398
import PlattCertificates.Count131072.C017399
import PlattCertificates.Count131072.C017400
import PlattCertificates.Count131072.C017401
import PlattCertificates.Count131072.C017402
import PlattCertificates.Count131072.C017403
import PlattCertificates.Count131072.C017404
import PlattCertificates.Count131072.C017405
import PlattCertificates.Count131072.C017406
import PlattCertificates.Count131072.C017407
import PlattCertificates.Count131072.C017408
import PlattCertificates.Count131072.C017409
import PlattCertificates.Count131072.C017410
import PlattCertificates.Count131072.C017411
import PlattCertificates.Count131072.C017412
import PlattCertificates.Count131072.C017413
import PlattCertificates.Count131072.C017414
import PlattCertificates.Count131072.C017415
import PlattCertificates.Count131072.C017416
import PlattCertificates.Count131072.C017417
import PlattCertificates.Count131072.C017418
import PlattCertificates.Count131072.C017419
import PlattCertificates.Count131072.C017420
import PlattCertificates.Count131072.C017421
import PlattCertificates.Count131072.C017422
import PlattCertificates.Count131072.C017423
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000231
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17392 : List PrefixCut := [⟨60,346856637,346856853⟩,
⟨128,745841270,745841730⟩]
theorem checked17392 : checkPrefixCuts (2^48) 2283536385 9 Manual.Count131072.C017392.packed 128 cuts17392 = true := by
 decide +kernel
def pointBounds17392 : List (Nat × Nat × Nat) := [(2283597824,98204925908919,98205305184426)]
theorem point_links_checked17392 : (cuts17392.take 1).map (fun c => (2283536385-1+2*2^9*c.k,98204579052282+c.lower,98204958327573+c.upper)) = pointBounds17392 := by
 decide +kernel
def cuts17393 : List PrefixCut := [⟨2,11955791,11955799⟩,
⟨72,420541489,420541749⟩,
⟨128,751221547,751222013⟩]
theorem checked17393 : checkPrefixCuts (2^48) 2283667457 9 Manual.Count131072.C017393.packed 128 cuts17393 = true := by
 decide +kernel
def pointBounds17393 : List (Nat × Nat × Nat) := [(2283669504,98205336849343,98205716125102),(2283741184,98205745435041,98206124711052)]
theorem point_links_checked17393 : (cuts17393.take 2).map (fun c => (2283667457-1+2*2^9*c.k,98205324893552+c.lower,98205704169303+c.upper)) = pointBounds17393 := by
 decide +kernel
def cuts17394 : List PrefixCut := [⟨14,81343800,81343851⟩,
⟨84,493477972,493478279⟩,
⟨128,756970883,756971350⟩]
theorem checked17394 : checkPrefixCuts (2^48) 2283798529 9 Manual.Count131072.C017394.packed 128 cuts17394 = true := by
 decide +kernel
def pointBounds17394 : List (Nat × Nat × Nat) := [(2283812864,98206157458899,98206536735167),(2283884544,98206569593071,98206948869595)]
theorem point_links_checked17394 : (cuts17394.take 2).map (fun c => (2283798529-1+2*2^9*c.k,98206076115099+c.lower,98206455391316+c.upper)) = pointBounds17394 := by
 decide +kernel
def cuts17395 : List PrefixCut := [⟨26,152448826,152448916⟩,
⟨96,556176910,556177247⟩,
⟨128,744726922,744727376⟩]
theorem checked17395 : checkPrefixCuts (2^48) 2283929601 9 Manual.Count131072.C017395.packed 128 cuts17395 = true := by
 decide +kernel
def pointBounds17395 : List (Nat × Nat × Nat) := [(2283956224,98206985534808,98207364811582),(2284027904,98207389262892,98207768539913)]
theorem point_links_checked17395 : (cuts17395.take 2).map (fun c => (2283929601-1+2*2^9*c.k,98206833085982+c.lower,98207212362666+c.upper)) = pointBounds17395 := by
 decide +kernel
def cuts17396 : List PrefixCut := [⟨38,227612005,227612143⟩,
⟨108,637476256,637476654⟩,
⟨128,753310473,753310945⟩]
theorem checked17396 : checkPrefixCuts (2^48) 2284060673 9 Manual.Count131072.C017396.packed 128 cuts17396 = true := by
 decide +kernel
def pointBounds17396 : List (Nat × Nat × Nat) := [(2284099584,98207805424909,98208184702185),(2284171264,98208215289160,98208594566696)]
theorem point_links_checked17396 : (cuts17396.take 2).map (fun c => (2284060673-1+2*2^9*c.k,98207577812904+c.lower,98207957090042+c.upper)) = pointBounds17396 := by
 decide +kernel
def cuts17397 : List PrefixCut := [⟨50,293770663,293770844⟩,
⟨120,703732388,703732824⟩,
⟨128,750679401,750679863⟩]
theorem checked17397 : checkPrefixCuts (2^48) 2284191745 9 Manual.Count131072.C017397.packed 128 cuts17397 = true := by
 decide +kernel
def pointBounds17397 : List (Nat × Nat × Nat) := [(2284242944,98208624894040,98209004171831),(2284314624,98209034855765,98209414133811)]
theorem point_links_checked17397 : (cuts17397.take 2).map (fun c => (2284191745-1+2*2^9*c.k,98208331123377+c.lower,98208710400987+c.upper)) = pointBounds17397 := by
 decide +kernel
def cuts17398 : List PrefixCut := [⟨62,368423520,368423751⟩,
⟨128,745584744,745585216⟩]
theorem checked17398 : checkPrefixCuts (2^48) 2284322817 9 Manual.Count131072.C017398.packed 128 cuts17398 = true := by
 decide +kernel
def pointBounds17398 : List (Nat × Nat × Nat) := [(2284386304,98209450226298,98209829504601)]
theorem point_links_checked17398 : (cuts17398.take 1).map (fun c => (2284322817-1+2*2^9*c.k,98209081802778+c.lower,98209461080850+c.upper)) = pointBounds17398 := by
 decide +kernel
def cuts17399 : List PrefixCut := [⟨4,24272979,24272994⟩,
⟨74,429267702,429267974⟩,
⟨128,743693627,743694092⟩]
theorem checked17399 : checkPrefixCuts (2^48) 2284453889 9 Manual.Count131072.C017399.packed 128 cuts17399 = true := by
 decide +kernel
def pointBounds17399 : List (Nat × Nat × Nat) := [(2284457984,98209851660501,98210230939060),(2284529664,98210256655224,98210635934040)]
theorem point_links_checked17399 : (cuts17399.take 2).map (fun c => (2284453889-1+2*2^9*c.k,98209827387522+c.lower,98210206666066+c.upper)) = pointBounds17399 := by
 decide +kernel
def cuts17400 : List PrefixCut := [⟨16,91172219,91172280⟩,
⟨86,498852065,498852381⟩,
⟨128,747716509,747716985⟩]
theorem checked17400 : checkPrefixCuts (2^48) 2284584961 9 Manual.Count131072.C017400.packed 128 cuts17400 = true := by
 decide +kernel
def pointBounds17400 : List (Nat × Nat × Nat) := [(2284601344,98210662253368,98211041532438),(2284673024,98211069933214,98211449212539)]
theorem point_links_checked17400 : (cuts17400.take 2).map (fun c => (2284584961-1+2*2^9*c.k,98210571081149+c.lower,98210950360158+c.upper)) = pointBounds17400 := by
 decide +kernel
def cuts17401 : List PrefixCut := [⟨28,164346534,164346638⟩,
⟨98,566087292,566087644⟩,
⟨128,743608167,743608628⟩]
theorem checked17401 : checkPrefixCuts (2^48) 2284716033 9 Manual.Count131072.C017401.packed 128 cuts17401 = true := by
 decide +kernel
def pointBounds17401 : List (Nat × Nat × Nat) := [(2284744704,98211483144192,98211862423781),(2284816384,98211884884950,98212264164787)]
theorem point_links_checked17401 : (cuts17401.take 2).map (fun c => (2284716033-1+2*2^9*c.k,98211318797658+c.lower,98211698077143+c.upper)) = pointBounds17401 := by
 decide +kernel
def cuts17402 : List PrefixCut := [⟨40,227533563,227533703⟩,
⟨110,633314430,633314819⟩,
⟨128,739500265,739500720⟩]
theorem checked17402 : checkPrefixCuts (2^48) 2284847105 9 Manual.Count131072.C017402.packed 128 cuts17402 = true := by
 decide +kernel
def pointBounds17402 : List (Nat × Nat × Nat) := [(2284888064,98212289939388,98212669219474),(2284959744,98212695720255,98213075000590)]
theorem point_links_checked17402 : (cuts17402.take 2).map (fun c => (2284847105-1+2*2^9*c.k,98212062405825+c.lower,98212441685771+c.upper)) = pointBounds17402 := by
 decide +kernel
def cuts17403 : List PrefixCut := [⟨52,306357341,306357528⟩,
⟨122,725046656,725047101⟩,
⟨128,759413327,759413793⟩]
theorem checked17403 : checkPrefixCuts (2^48) 2284978177 9 Manual.Count131072.C017403.packed 128 cuts17403 = true := by
 decide +kernel
def pointBounds17403 : List (Nat × Nat × Nat) := [(2285031424,98213108263431,98213487544019),(2285103104,98213526952746,98213906233592)]
theorem point_links_checked17403 : (cuts17403.take 2).map (fun c => (2284978177-1+2*2^9*c.k,98212801906090+c.lower,98213181186491+c.upper)) = pointBounds17403 := by
 decide +kernel
def cuts17404 : List PrefixCut := [⟨64,381106890,381107123⟩,
⟨128,759739426,759739893⟩]
theorem checked17404 : checkPrefixCuts (2^48) 2285109249 9 Manual.Count131072.C017404.packed 128 cuts17404 = true := by
 decide +kernel
def pointBounds17404 : List (Nat × Nat × Nat) := [(2285174784,98213942426307,98214321707407)]
theorem point_links_checked17404 : (cuts17404.take 1).map (fun c => (2285109249-1+2*2^9*c.k,98213561319417+c.lower,98213940600284+c.upper)) = pointBounds17404 := by
 decide +kernel
def cuts17405 : List PrefixCut := [⟨6,36212168,36212190⟩,
⟨76,442791526,442791800⟩,
⟨128,744053515,744053974⟩]
theorem checked17405 : checkPrefixCuts (2^48) 2285240321 9 Manual.Count131072.C017405.packed 128 cuts17405 = true := by
 decide +kernel
def pointBounds17405 : List (Nat × Nat × Nat) := [(2285246464,98214357271011,98214736552367),(2285318144,98214763850369,98215143131977)]
theorem point_links_checked17405 : (cuts17405.take 2).map (fun c => (2285240321-1+2*2^9*c.k,98214321058843+c.lower,98214700340177+c.upper)) = pointBounds17405 := by
 decide +kernel
def cuts17406 : List PrefixCut := [⟨18,105427744,105427810⟩,
⟨88,514568025,514568337⟩,
⟨128,749553068,749553526⟩]
theorem checked17406 : checkPrefixCuts (2^48) 2285371393 9 Manual.Count131072.C017406.packed 128 cuts17406 = true := by
 decide +kernel
def pointBounds17406 : List (Nat × Nat × Nat) := [(2285389824,98215170540102,98215549821961),(2285461504,98215579680383,98215958962488)]
theorem point_links_checked17406 : (cuts17406.take 2).map (fun c => (2285371393-1+2*2^9*c.k,98215065112358+c.lower,98215444394151+c.upper)) = pointBounds17406 := by
 decide +kernel
def cuts17407 : List PrefixCut := [⟨30,172541342,172541446⟩,
⟨100,583010624,583010991⟩,
⟨128,746677486,746677954⟩]
theorem checked17407 : checkPrefixCuts (2^48) 2285502465 9 Manual.Count131072.C017407.packed 128 cuts17407 = true := by
 decide +kernel
def pointBounds17407 : List (Nat × Nat × Nat) := [(2285533184,98215987206768,98216366489123),(2285604864,98216397676050,98216776958668)]
theorem point_links_checked17407 : (cuts17407.take 2).map (fun c => (2285502465-1+2*2^9*c.k,98215814665426+c.lower,98216193947677+c.upper)) = pointBounds17407 := by
 decide +kernel
def cuts17408 : List PrefixCut := [⟨42,249498714,249498865⟩,
⟨112,653784962,653785360⟩,
⟨128,750205926,750206385⟩]
theorem checked17408 : checkPrefixCuts (2^48) 2285633537 9 Manual.Count131072.C017408.packed 128 cuts17408 = true := by
 decide +kernel
def pointBounds17408 : List (Nat × Nat × Nat) := [(2285676544,98216810841626,98217190124496),(2285748224,98217215127874,98217594410991)]
theorem point_links_checked17408 : (cuts17408.take 2).map (fun c => (2285633537-1+2*2^9*c.k,98216561342912+c.lower,98216940625631+c.upper)) = pointBounds17408 := by
 decide +kernel
def cuts17409 : List PrefixCut := [⟨54,324969258,324969458⟩,
⟨124,736987710,736988168⟩,
⟨128,760876017,760876488⟩]
theorem checked17409 : checkPrefixCuts (2^48) 2285764609 9 Manual.Count131072.C017409.packed 128 cuts17409 = true := by
 decide +kernel
def pointBounds17409 : List (Nat × Nat × Nat) := [(2285819904,98217636518096,98218015801474),(2285891584,98218048536548,98218427820184)]
theorem point_links_checked17409 : (cuts17409.take 2).map (fun c => (2285764609-1+2*2^9*c.k,98217311548838+c.lower,98217690832016+c.upper)) = pointBounds17409 := by
 decide +kernel
def cuts17410 : List PrefixCut := [⟨66,379005464,379005693⟩,
⟨128,740638659,740639110⟩]
theorem checked17410 : checkPrefixCuts (2^48) 2285895681 9 Manual.Count131072.C017410.packed 128 cuts17410 = true := by
 decide +kernel
def pointBounds17410 : List (Nat × Nat × Nat) := [(2285963264,98218451430319,98218830714197)]
theorem point_links_checked17410 : (cuts17410.take 1).map (fun c => (2285895681-1+2*2^9*c.k,98218072424855+c.lower,98218451708504+c.upper)) = pointBounds17410 := by
 decide +kernel
def cuts17411 : List PrefixCut := [⟨8,48512515,48512544⟩,
⟨78,460246079,460246364⟩,
⟨128,747983941,747984405⟩]
theorem checked17411 : checkPrefixCuts (2^48) 2286026753 9 Manual.Count131072.C017411.packed 128 cuts17411 = true := by
 decide +kernel
def pointBounds17411 : List (Nat × Nat × Nat) := [(2286034944,98218861576029,98219240860158),(2286106624,98219273309593,98219652593978)]
theorem point_links_checked17411 : (cuts17411.take 2).map (fun c => (2286026753-1+2*2^9*c.k,98218813063514+c.lower,98219192347614+c.upper)) = pointBounds17411 := by
 decide +kernel
def cuts17412 : List PrefixCut := [⟨20,118688458,118688530⟩,
⟨90,532119818,532120142⟩,
⟨128,758652089,758652554⟩]
theorem checked17412 : checkPrefixCuts (2^48) 2286157825 9 Manual.Count131072.C017412.packed 128 cuts17412 = true := by
 decide +kernel
def pointBounds17412 : List (Nat × Nat × Nat) := [(2286178304,98219679735913,98220059020549),(2286249984,98220093167273,98220472452161)]
theorem point_links_checked17412 : (cuts17412.take 2).map (fun c => (2286157825-1+2*2^9*c.k,98219561047455+c.lower,98219940332019+c.upper)) = pointBounds17412 := by
 decide +kernel
def cuts17413 : List PrefixCut := [⟨32,188979106,188979222⟩,
⟨102,604846824,604847196⟩,
⟨128,760209074,760209541⟩]
theorem checked17413 : checkPrefixCuts (2^48) 2286288897 9 Manual.Count131072.C017413.packed 128 cuts17413 = true := by
 decide +kernel
def pointBounds17413 : List (Nat × Nat × Nat) := [(2286321664,98220508678650,98220887963795),(2286393344,98220924546368,98221303831769)]
theorem point_links_checked17413 : (cuts17413.take 2).map (fun c => (2286288897-1+2*2^9*c.k,98220319699544+c.lower,98220698984573+c.upper)) = pointBounds17413 := by
 decide +kernel
def cuts17414 : List PrefixCut := [⟨44,253844668,253844824⟩,
⟨114,662915610,662916024⟩,
⟨128,749455323,749455788⟩]
theorem checked17414 : checkPrefixCuts (2^48) 2286419969 9 Manual.Count131072.C017414.packed 128 cuts17414 = true := by
 decide +kernel
def pointBounds17414 : List (Nat × Nat × Nat) := [(2286465024,98221333753286,98221713038938),(2286536704,98221742824228,98222122110138)]
theorem point_links_checked17414 : (cuts17414.take 2).map (fun c => (2286419969-1+2*2^9*c.k,98221079908618+c.lower,98221459194114+c.upper)) = pointBounds17414 := by
 decide +kernel
def cuts17415 : List PrefixCut := [⟨56,335320701,335320907⟩,
⟨126,743996717,743997178⟩,
⟨128,754952011,754952479⟩]
theorem checked17415 : checkPrefixCuts (2^48) 2286551041 9 Manual.Count131072.C017415.packed 128 cuts17415 = true := by
 decide +kernel
def pointBounds17415 : List (Nat × Nat × Nat) := [(2286608384,98222164684642,98222543970809),(2286680064,98222573360658,98222952647080)]
theorem point_links_checked17415 : (cuts17415.take 2).map (fun c => (2286551041-1+2*2^9*c.k,98221829363941+c.lower,98222208649902+c.upper)) = pointBounds17415 := by
 decide +kernel
def cuts17416 : List PrefixCut := [⟨68,393892060,393892304⟩,
⟨128,746046112,746046571⟩]
theorem checked17416 : checkPrefixCuts (2^48) 2286682113 9 Manual.Count131072.C017416.packed 128 cuts17416 = true := by
 decide +kernel
def pointBounds17416 : List (Nat × Nat × Nat) := [(2286751744,98222978208012,98223357494685)]
theorem point_links_checked17416 : (cuts17416.take 1).map (fun c => (2286682113-1+2*2^9*c.k,98222584315952+c.lower,98222963602381+c.upper)) = pointBounds17416 := by
 decide +kernel
def cuts17417 : List PrefixCut := [⟨10,58342675,58342710⟩,
⟨80,477688541,477688832⟩,
⟨128,758188691,758189153⟩]
theorem checked17417 : checkPrefixCuts (2^48) 2286813185 9 Manual.Count131072.C017417.packed 128 cuts17417 = true := by
 decide +kernel
def pointBounds17417 : List (Nat × Nat × Nat) := [(2286823424,98223388704739,98223767991662),(2286895104,98223808050605,98224187337784)]
theorem point_links_checked17417 : (cuts17417.take 2).map (fun c => (2286813185-1+2*2^9*c.k,98223330362064+c.lower,98223709648952+c.upper)) = pointBounds17417 := by
 decide +kernel
def cuts17418 : List PrefixCut := [⟨22,128493874,128493950⟩,
⟨92,539936657,539936981⟩,
⟨128,752483684,752484134⟩]
theorem checked17418 : checkPrefixCuts (2^48) 2286944257 9 Manual.Count131072.C017418.packed 128 cuts17418 = true := by
 decide +kernel
def pointBounds17418 : List (Nat × Nat × Nat) := [(2286966784,98224217044629,98224596332055),(2287038464,98224628487412,98225007775086)]
theorem point_links_checked17418 : (cuts17418.take 2).map (fun c => (2286944257-1+2*2^9*c.k,98224088550755+c.lower,98224467838105+c.upper)) = pointBounds17418 := by
 decide +kernel
def cuts17419 : List PrefixCut := [⟨34,197898227,197898346⟩,
⟨104,601192639,601193005⟩,
⟨128,745671646,745672102⟩]
theorem checked17419 : checkPrefixCuts (2^48) 2287075329 9 Manual.Count131072.C017419.packed 128 cuts17419 = true := by
 decide +kernel
def pointBounds17419 : List (Nat × Nat × Nat) := [(2287110144,98225038932666,98225418220585),(2287181824,98225442227078,98225821515244)]
theorem point_links_checked17419 : (cuts17419.take 2).map (fun c => (2287075329-1+2*2^9*c.k,98224841034439+c.lower,98225220322239+c.upper)) = pointBounds17419 := by
 decide +kernel
def cuts17420 : List PrefixCut := [⟨46,278616161,278616331⟩,
⟨116,684838798,684839222⟩,
⟨128,754243626,754244092⟩]
theorem checked17420 : checkPrefixCuts (2^48) 2287206401 9 Manual.Count131072.C017420.packed 128 cuts17420 = true := by
 decide +kernel
def pointBounds17420 : List (Nat × Nat × Nat) := [(2287253504,98225865322246,98226244610672),(2287325184,98226271544883,98226650833563)]
theorem point_links_checked17420 : (cuts17420.take 2).map (fun c => (2287206401-1+2*2^9*c.k,98225586706085+c.lower,98225965994341+c.upper)) = pointBounds17420 := by
 decide +kernel
def cuts17421 : List PrefixCut := [⟨58,334343955,334344164⟩,
⟨128,744232767,744233229⟩]
theorem checked17421 : checkPrefixCuts (2^48) 2287337473 9 Manual.Count131072.C017421.packed 128 cuts17421 = true := by
 decide +kernel
def pointBounds17421 : List (Nat × Nat × Nat) := [(2287396864,98226675293666,98227054582597),(2287468544,98227085182478,98227464471662)]
theorem point_links_checked17421 : (cuts17421.take 2).map (fun c => (2287337473-1+2*2^9*c.k,98226340949711+c.lower,98226720238433+c.upper)) = pointBounds17421 := by
 decide +kernel
def cuts17422 : List PrefixCut := [⟨70,409999005,409999257⟩,
⟨128,746774249,746774706⟩]
theorem checked17422 : checkPrefixCuts (2^48) 2287468545 9 Manual.Count131072.C017422.packed 128 cuts17422 = true := by
 decide +kernel
def pointBounds17422 : List (Nat × Nat × Nat) := [(2287540224,98227495181483,98227874470919)]
theorem point_links_checked17422 : (cuts17422.take 1).map (fun c => (2287468545-1+2*2^9*c.k,98227085182478+c.lower,98227464471662+c.upper)) = pointBounds17422 := by
 decide +kernel
def cuts17423 : List PrefixCut := [⟨12,67427812,67427854⟩,
⟨82,471494991,471495288⟩,
⟨128,746361846,746362312⟩]
theorem checked17423 : checkPrefixCuts (2^48) 2287599617 9 Manual.Count131072.C017423.packed 128 cuts17423 = true := by
 decide +kernel
def pointBounds17423 : List (Nat × Nat × Nat) := [(2287611904,98227899384539,98228278674222),(2287683584,98228303451718,98228682741656)]
theorem point_links_checked17423 : (cuts17423.take 2).map (fun c => (2287599617-1+2*2^9*c.k,98227831956727+c.lower,98228211246368+c.upper)) = pointBounds17423 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000231
