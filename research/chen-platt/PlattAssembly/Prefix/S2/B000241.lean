import PlattAssemblyKernel
import PlattCertificates.Count131072.C017712
import PlattCertificates.Count131072.C017713
import PlattCertificates.Count131072.C017714
import PlattCertificates.Count131072.C017715
import PlattCertificates.Count131072.C017716
import PlattCertificates.Count131072.C017717
import PlattCertificates.Count131072.C017718
import PlattCertificates.Count131072.C017719
import PlattCertificates.Count131072.C017720
import PlattCertificates.Count131072.C017721
import PlattCertificates.Count131072.C017722
import PlattCertificates.Count131072.C017723
import PlattCertificates.Count131072.C017724
import PlattCertificates.Count131072.C017725
import PlattCertificates.Count131072.C017726
import PlattCertificates.Count131072.C017727
import PlattCertificates.Count131072.C017728
import PlattCertificates.Count131072.C017729
import PlattCertificates.Count131072.C017730
import PlattCertificates.Count131072.C017731
import PlattCertificates.Count131072.C017732
import PlattCertificates.Count131072.C017733
import PlattCertificates.Count131072.C017734
import PlattCertificates.Count131072.C017735
import PlattCertificates.Count131072.C017736
import PlattCertificates.Count131072.C017737
import PlattCertificates.Count131072.C017738
import PlattCertificates.Count131072.C017739
import PlattCertificates.Count131072.C017740
import PlattCertificates.Count131072.C017741
import PlattCertificates.Count131072.C017742
import PlattCertificates.Count131072.C017743
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000241
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17712 : List PrefixCut := [⟨66,377153720,377153950⟩,
⟨128,736020545,736020992⟩]
theorem checked17712 : checkPrefixCuts (2^48) 2325479425 9 Manual.Count131072.C017712.packed 128 cuts17712 = true := by
 decide +kernel
def pointBounds17712 : List (Nat × Nat × Nat) := [(2325547008,98442620958614,98443000380758)]
theorem point_links_checked17712 : (cuts17712.take 1).map (fun c => (2325479425-1+2*2^9*c.k,98442243804894+c.lower,98442623226808+c.upper)) = pointBounds17712 := by
 decide +kernel
def cuts17713 : List PrefixCut := [⟨9,51438790,51438821⟩,
⟨80,463668123,463668411⟩,
⟨128,739004882,739005336⟩]
theorem checked17713 : checkPrefixCuts (2^48) 2325610497 9 Manual.Count131072.C017713.packed 128 cuts17713 = true := by
 decide +kernel
def pointBounds17713 : List (Nat × Nat × Nat) := [(2325619712,98443031264229,98443410686621),(2325692416,98443443493562,98443822916211)]
theorem point_links_checked17713 : (cuts17713.take 2).map (fun c => (2325610497-1+2*2^9*c.k,98442979825439+c.lower,98443359247800+c.upper)) = pointBounds17713 := by
 decide +kernel
def cuts17714 : List PrefixCut := [⟨23,133127767,133127851⟩,
⟨94,539280108,539280438⟩,
⟨128,740294216,740294668⟩]
theorem checked17714 : checkPrefixCuts (2^48) 2325741569 9 Manual.Count131072.C017714.packed 128 cuts17714 = true := by
 decide +kernel
def pointBounds17714 : List (Nat × Nat × Nat) := [(2325765120,98443851958088,98444231380987),(2325837824,98444258110429,98444637533574)]
theorem point_links_checked17714 : (cuts17714.take 2).map (fun c => (2325741569-1+2*2^9*c.k,98443718830321+c.lower,98444098253136+c.upper)) = pointBounds17714 := by
 decide +kernel
def cuts17715 : List PrefixCut := [⟨37,212507716,212507846⟩,
⟨108,622023083,622023462⟩,
⟨128,737590256,737590705⟩]
theorem checked17715 : checkPrefixCuts (2^48) 2325872641 9 Manual.Count131072.C017715.packed 128 cuts17715 = true := by
 decide +kernel
def pointBounds17715 : List (Nat × Nat × Nat) := [(2325910528,98444671632253,98445051055650),(2325983232,98445081147620,98445460571266)]
theorem point_links_checked17715 : (cuts17715.take 2).map (fun c => (2325872641-1+2*2^9*c.k,98444459124537+c.lower,98444838547804+c.upper)) = pointBounds17715 := by
 decide +kernel
def cuts17716 : List PrefixCut := [⟨51,288368885,288369058⟩,
⟨122,697374593,697375016⟩,
⟨128,731498162,731498606⟩]
theorem checked17716 : checkPrefixCuts (2^48) 2326003713 9 Manual.Count131072.C017716.packed 128 cuts17716 = true := by
 decide +kernel
def pointBounds17716 : List (Nat × Nat × Nat) := [(2326055936,98445485083678,98445864507567),(2326128640,98445894089386,98446273513525)]
theorem point_links_checked17716 : (cuts17716.take 2).map (fun c => (2326003713-1+2*2^9*c.k,98445196714793+c.lower,98445576138509+c.upper)) = pointBounds17716 := by
 decide +kernel
def cuts17717 : List PrefixCut := [⟨65,379588507,379588740⟩,
⟨128,737386278,737386733⟩]
theorem checked17717 : checkPrefixCuts (2^48) 2326134785 9 Manual.Count131072.C017717.packed 128 cuts17717 = true := by
 decide +kernel
def pointBounds17717 : List (Nat × Nat × Nat) := [(2326201344,98446307801462,98446687225855)]
theorem point_links_checked17717 : (cuts17717.take 1).map (fun c => (2326134785-1+2*2^9*c.k,98445928212955+c.lower,98446307637115+c.upper)) = pointBounds17717 := by
 decide +kernel
def cuts17718 : List PrefixCut := [⟨8,45495390,45495418⟩,
⟨79,446477075,446477354⟩,
⟨128,729358896,729359353⟩]
theorem checked17718 : checkPrefixCuts (2^48) 2326265857 9 Manual.Count131072.C017718.packed 128 cuts17718 = true := by
 decide +kernel
def pointBounds17718 : List (Nat × Nat × Nat) := [(2326274048,98446711094623,98447090519266),(2326346752,98447112076308,98447491501202)]
theorem point_links_checked17718 : (cuts17718.take 2).map (fun c => (2326265857-1+2*2^9*c.k,98446665599233+c.lower,98447045023848+c.upper)) = pointBounds17718 := by
 decide +kernel
def cuts17719 : List PrefixCut := [⟨22,126193802,126193880⟩,
⟨93,530417150,530417477⟩,
⟨128,734520330,734520783⟩]
theorem checked17719 : checkPrefixCuts (2^48) 2326396929 9 Manual.Count131072.C017719.packed 128 cuts17719 = true := by
 decide +kernel
def pointBounds17719 : List (Nat × Nat × Nat) := [(2326419456,98447521151931,98447900577081),(2326492160,98447925375279,98448304800678)]
theorem point_links_checked17719 : (cuts17719.take 2).map (fun c => (2326396929-1+2*2^9*c.k,98447394958129+c.lower,98447774383201+c.upper)) = pointBounds17719 := by
 decide +kernel
def cuts17720 : List PrefixCut := [⟨36,210149185,210149312⟩,
⟨108,626082323,626082704⟩,
⟨128,742221846,742222297⟩]
theorem checked17720 : checkPrefixCuts (2^48) 2326528001 9 Manual.Count131072.C017720.packed 128 cuts17720 = true := by
 decide +kernel
def pointBounds17720 : List (Nat × Nat × Nat) := [(2326564864,98448339627644,98448719053296),(2326638592,98448755560782,98449134986688)]
theorem point_links_checked17720 : (cuts17720.take 2).map (fun c => (2326528001-1+2*2^9*c.k,98448129478459+c.lower,98448508903984+c.upper)) = pointBounds17720 := by
 decide +kernel
def cuts17721 : List PrefixCut := [⟨52,299296479,299296658⟩,
⟨124,717259764,717260198⟩,
⟨128,741937936,741938385⟩]
theorem checked17721 : checkPrefixCuts (2^48) 2326659073 9 Manual.Count131072.C017721.packed 128 cuts17721 = true := by
 decide +kernel
def pointBounds17721 : List (Nat × Nat × Nat) := [(2326712320,98449170996784,98449550422939),(2326786048,98449588960069,98449968386479)]
theorem point_links_checked17721 : (cuts17721.take 2).map (fun c => (2326659073-1+2*2^9*c.k,98448871700305+c.lower,98449251126281+c.upper)) = pointBounds17721 := by
 decide +kernel
def cuts17722 : List PrefixCut := [⟨68,389400855,389401095⟩,
⟨128,732823610,732824061⟩]
theorem checked17722 : checkPrefixCuts (2^48) 2326790145 9 Manual.Count131072.C017722.packed 128 cuts17722 = true := by
 decide +kernel
def pointBounds17722 : List (Nat × Nat × Nat) := [(2326859776,98450003039096,98450382465761)]
theorem point_links_checked17722 : (cuts17722.take 1).map (fun c => (2326790145-1+2*2^9*c.k,98449613638241+c.lower,98449993064666+c.upper)) = pointBounds17722 := by
 decide +kernel
def cuts17723 : List PrefixCut := [⟨12,71005981,71006025⟩,
⟨84,474776975,474777277⟩,
⟨128,728427737,728428193⟩]
theorem checked17723 : checkPrefixCuts (2^48) 2326921217 9 Manual.Count131072.C017723.packed 128 cuts17723 = true := by
 decide +kernel
def pointBounds17723 : List (Nat × Nat × Nat) := [(2326933504,98450417467832,98450796894752),(2327007232,98450821238826,98451200666004)]
theorem point_links_checked17723 : (cuts17723.take 2).map (fun c => (2326921217-1+2*2^9*c.k,98450346461851+c.lower,98450725888727+c.upper)) = pointBounds17723 := by
 decide +kernel
def cuts17724 : List PrefixCut := [⟨28,160146980,160147081⟩,
⟨100,572359197,572359550⟩,
⟨128,736490578,736491033⟩]
theorem checked17724 : checkPrefixCuts (2^48) 2327052289 9 Manual.Count131072.C017724.packed 128 cuts17724 = true := by
 decide +kernel
def pointBounds17724 : List (Nat × Nat × Nat) := [(2327080960,98451235036568,98451614464001),(2327154688,98451647248785,98452026676470)]
theorem point_links_checked17724 : (cuts17724.take 2).map (fun c => (2327052289-1+2*2^9*c.k,98451074889588+c.lower,98451454316920+c.upper)) = pointBounds17724 := by
 decide +kernel
def cuts17725 : List PrefixCut := [⟨44,245527967,245528114⟩,
⟨116,663398551,663398950⟩,
⟨128,734030078,734030521⟩]
theorem checked17725 : checkPrefixCuts (2^48) 2327183361 9 Manual.Count131072.C017725.packed 128 cuts17725 = true := by
 decide +kernel
def pointBounds17725 : List (Nat × Nat × Nat) := [(2327228416,98452056908133,98452436336067),(2327302144,98452474778717,98452854206903)]
theorem point_links_checked17725 : (cuts17725.take 2).map (fun c => (2327183361-1+2*2^9*c.k,98451811380166+c.lower,98452190807953+c.upper)) = pointBounds17725 := by
 decide +kernel
def cuts17726 : List PrefixCut := [⟨60,342146231,342146441⟩,
⟨128,726490627,726491079⟩]
theorem checked17726 : checkPrefixCuts (2^48) 2327314433 9 Manual.Count131072.C017726.packed 128 cuts17726 = true := by
 decide +kernel
def pointBounds17726 : List (Nat × Nat × Nat) := [(2327375872,98452887556475,98453266984915)]
theorem point_links_checked17726 : (cuts17726.take 1).map (fun c => (2327314433-1+2*2^9*c.k,98452545410244+c.lower,98452924838474+c.upper)) = pointBounds17726 := by
 decide +kernel
def cuts17727 : List PrefixCut := [⟨4,23945556,23945571⟩,
⟨76,435366912,435367178⟩,
⟨128,735156974,735157426⟩]
theorem checked17727 : checkPrefixCuts (2^48) 2327445505 9 Manual.Count131072.C017727.packed 128 cuts17727 = true := by
 decide +kernel
def pointBounds17727 : List (Nat × Nat × Nat) := [(2327449600,98453295846427,98453675275124),(2327523328,98453707267783,98454086696731)]
theorem point_links_checked17727 : (cuts17727.take 2).map (fun c => (2327445505-1+2*2^9*c.k,98453271900871+c.lower,98453651329553+c.upper)) = pointBounds17727 := by
 decide +kernel
def cuts17728 : List PrefixCut := [⟨20,116213660,116213728⟩,
⟨92,530511174,530511501⟩,
⟨128,737655049,737655505⟩]
theorem checked17728 : checkPrefixCuts (2^48) 2327576577 9 Manual.Count131072.C017728.packed 128 cuts17728 = true := by
 decide +kernel
def pointBounds17728 : List (Nat × Nat × Nat) := [(2327597056,98454123271505,98454502700707),(2327670784,98454537569019,98454916998480)]
theorem point_links_checked17728 : (cuts17728.take 2).map (fun c => (2327576577-1+2*2^9*c.k,98454007057845+c.lower,98454386486979+c.upper)) = pointBounds17728 := by
 decide +kernel
def cuts17729 : List PrefixCut := [⟨36,210405473,210405598⟩,
⟨108,629150804,629151185⟩,
⟨128,748496248,748496698⟩]
theorem checked17729 : checkPrefixCuts (2^48) 2327707649 9 Manual.Count131072.C017729.packed 128 cuts17729 = true := by
 decide +kernel
def pointBounds17729 : List (Nat × Nat × Nat) := [(2327744512,98454955118367,98455334548082),(2327818240,98455373863698,98455753293669)]
theorem point_links_checked17729 : (cuts17729.take 2).map (fun c => (2327707649-1+2*2^9*c.k,98454744712894+c.lower,98455124142484+c.upper)) = pointBounds17729 := by
 decide +kernel
def cuts17730 : List PrefixCut := [⟨52,291164457,291164638⟩,
⟨124,703837677,703838112⟩,
⟨128,725843321,725843769⟩]
theorem checked17730 : checkPrefixCuts (2^48) 2327838721 9 Manual.Count131072.C017730.packed 128 cuts17730 = true := by
 decide +kernel
def pointBounds17730 : List (Nat × Nat × Nat) := [(2327891968,98455784373599,98456163803820),(2327965696,98456197046819,98456576477294)]
theorem point_links_checked17730 : (cuts17730.take 2).map (fun c => (2327838721-1+2*2^9*c.k,98455493209142+c.lower,98455872639182+c.upper)) = pointBounds17730 := by
 decide +kernel
def cuts17731 : List PrefixCut := [⟨68,391500762,391501004⟩,
⟨128,731001506,731001953⟩]
theorem checked17731 : checkPrefixCuts (2^48) 2327969793 9 Manual.Count131072.C017731.packed 128 cuts17731 = true := by
 decide +kernel
def pointBounds17731 : List (Nat × Nat × Nat) := [(2328039424,98456610553225,98456989983955)]
theorem point_links_checked17731 : (cuts17731.take 1).map (fun c => (2327969793-1+2*2^9*c.k,98456219052463+c.lower,98456598482951+c.upper)) = pointBounds17731 := by
 decide +kernel
def cuts17732 : List PrefixCut := [⟨12,70970004,70970048⟩,
⟨84,480823328,480823621⟩,
⟨128,730839525,730839974⟩]
theorem checked17732 : checkPrefixCuts (2^48) 2328100865 9 Manual.Count131072.C017732.packed 128 cuts17732 = true := by
 decide +kernel
def pointBounds17732 : List (Nat × Nat × Nat) := [(2328113152,98457021023973,98457400454952),(2328186880,98457430877297,98457810308525)]
theorem point_links_checked17732 : (cuts17732.take 2).map (fun c => (2328100865-1+2*2^9*c.k,98456950053969+c.lower,98457329484904+c.upper)) = pointBounds17732 := by
 decide +kernel
def cuts17733 : List PrefixCut := [⟨28,154383751,154383847⟩,
⟨100,558045536,558045878⟩,
⟨128,722335518,722335964⟩]
theorem checked17733 : checkPrefixCuts (2^48) 2328231937 9 Manual.Count131072.C017733.packed 128 cuts17733 = true := by
 decide +kernel
def pointBounds17733 : List (Nat × Nat × Nat) := [(2328260608,98457835277245,98458214708725),(2328334336,98458238939030,98458618370756)]
theorem point_links_checked17733 : (cuts17733.take 2).map (fun c => (2328231937-1+2*2^9*c.k,98457680893494+c.lower,98458060324878+c.upper)) = pointBounds17733 := by
 decide +kernel
def cuts17734 : List PrefixCut := [⟨44,250964391,250964537⟩,
⟨116,662941687,662942082⟩,
⟨128,732207720,732208156⟩]
theorem checked17734 : checkPrefixCuts (2^48) 2328363009 9 Manual.Count131072.C017734.packed 128 cuts17734 = true := by
 decide +kernel
def pointBounds17734 : List (Nat × Nat × Nat) := [(2328408064,98458654193403,98459033625379),(2328481792,98459066170699,98459445602924)]
theorem point_links_checked17734 : (cuts17734.take 2).map (fun c => (2328363009-1+2*2^9*c.k,98458403229012+c.lower,98458782660842+c.upper)) = pointBounds17734 := by
 decide +kernel
def cuts17735 : List PrefixCut := [⟨60,347049977,347050183⟩,
⟨128,738814915,738815364⟩]
theorem checked17735 : checkPrefixCuts (2^48) 2328494081 9 Manual.Count131072.C017735.packed 128 cuts17735 = true := by
 decide +kernel
def pointBounds17735 : List (Nat × Nat × Nat) := [(2328555520,98459482486709,98459861919181)]
theorem point_links_checked17735 : (cuts17735.take 1).map (fun c => (2328494081-1+2*2^9*c.k,98459135436732+c.lower,98459514868998+c.upper)) = pointBounds17735 := by
 decide +kernel
def cuts17736 : List PrefixCut := [⟨4,24054303,24054317⟩,
⟨76,432728842,432729114⟩,
⟨128,735509653,735510112⟩]
theorem checked17736 : checkPrefixCuts (2^48) 2328625153 9 Manual.Count131072.C017736.packed 128 cuts17736 = true := by
 decide +kernel
def pointBounds17736 : List (Nat × Nat × Nat) := [(2328629248,98459898305950,98460277738679),(2328702976,98460306980489,98460686413476)]
theorem point_links_checked17736 : (cuts17736.take 2).map (fun c => (2328625153-1+2*2^9*c.k,98459874251647+c.lower,98460253684362+c.upper)) = pointBounds17736 := by
 decide +kernel
def cuts17737 : List PrefixCut := [⟨20,116275666,116275738⟩,
⟨92,529517309,529517637⟩,
⟨128,730875649,730876098⟩]
theorem checked17737 : checkPrefixCuts (2^48) 2328756225 9 Manual.Count131072.C017737.packed 128 cuts17737 = true := by
 decide +kernel
def pointBounds17737 : List (Nat × Nat × Nat) := [(2328776704,98460726036966,98461105470212),(2328850432,98461139278609,98461518712111)]
theorem point_links_checked17737 : (cuts17737.take 2).map (fun c => (2328756225-1+2*2^9*c.k,98460609761300+c.lower,98460989194474+c.upper)) = pointBounds17737 := by
 decide +kernel
def cuts17738 : List PrefixCut := [⟨36,204376679,204376805⟩,
⟨108,610824052,610824431⟩,
⟨128,729021338,729021792⟩]
theorem checked17738 : checkPrefixCuts (2^48) 2328887297 9 Manual.Count131072.C017738.packed 128 cuts17738 = true := by
 decide +kernel
def pointBounds17738 : List (Nat × Nat × Nat) := [(2328924160,98461545013628,98461924447377),(2328997888,98461951461001,98462330895003)]
theorem point_links_checked17738 : (cuts17738.take 2).map (fun c => (2328887297-1+2*2^9*c.k,98461340636949+c.lower,98461720070572+c.upper)) = pointBounds17738 := by
 decide +kernel
def cuts17739 : List PrefixCut := [⟨52,299355862,299356045⟩,
⟨124,712907718,712908157⟩,
⟨128,736473252,736473705⟩]
theorem checked17739 : checkPrefixCuts (2^48) 2329018369 9 Manual.Count131072.C017739.packed 128 cuts17739 = true := by
 decide +kernel
def pointBounds17739 : List (Nat × Nat × Nat) := [(2329071616,98462369014149,98462748448409),(2329145344,98462782566005,98463162000521)]
theorem point_links_checked17739 : (cuts17739.take 2).map (fun c => (2329018369-1+2*2^9*c.k,98462069658287+c.lower,98462449092364+c.upper)) = pointBounds17739 := by
 decide +kernel
def cuts17740 : List PrefixCut := [⟨68,388039688,388039925⟩,
⟨128,730147905,730148350⟩]
theorem checked17740 : checkPrefixCuts (2^48) 2329149441 9 Manual.Count131072.C017740.packed 128 cuts17740 = true := by
 decide +kernel
def pointBounds17740 : List (Nat × Nat × Nat) := [(2329219072,98463194171227,98463573605994)]
theorem point_links_checked17740 : (cuts17740.take 1).map (fun c => (2329149441-1+2*2^9*c.k,98462806131539+c.lower,98463185566069+c.upper)) = pointBounds17740 := by
 decide +kernel
def cuts17741 : List PrefixCut := [⟨12,72625840,72625885⟩,
⟨84,482634172,482634470⟩,
⟨128,742794848,742795306⟩]
theorem checked17741 : checkPrefixCuts (2^48) 2329280513 9 Manual.Count131072.C017741.packed 128 cuts17741 = true := by
 decide +kernel
def pointBounds17741 : List (Nat × Nat × Nat) := [(2329292800,98463608905284,98463988340304),(2329366528,98464018913616,98464398348889)]
theorem point_links_checked17741 : (cuts17741.take 2).map (fun c => (2329280513-1+2*2^9*c.k,98463536279444+c.lower,98463915714419+c.upper)) = pointBounds17741 := by
 decide +kernel
def cuts17742 : List PrefixCut := [⟨28,162038986,162039087⟩,
⟨100,570087972,570088322⟩,
⟨128,736711342,736711795⟩]
theorem checked17742 : checkPrefixCuts (2^48) 2329411585 9 Manual.Count131072.C017742.packed 128 cuts17742 = true := by
 decide +kernel
def pointBounds17742 : List (Nat × Nat × Nat) := [(2329440256,98464441113278,98464820548812),(2329513984,98464849162264,98465228598047)]
theorem point_links_checked17742 : (cuts17742.take 2).map (fun c => (2329411585-1+2*2^9*c.k,98464279074292+c.lower,98464658509725+c.upper)) = pointBounds17742 := by
 decide +kernel
def cuts17743 : List PrefixCut := [⟨44,249870664,249870818⟩,
⟨116,659826880,659827293⟩,
⟨128,727124683,727125139⟩]
theorem checked17743 : checkPrefixCuts (2^48) 2329542657 9 Manual.Count131072.C017743.packed 128 cuts17743 = true := by
 decide +kernel
def pointBounds17743 : List (Nat × Nat × Nat) := [(2329587712,98465265656298,98465645092338),(2329661440,98465675612514,98466055048813)]
theorem point_links_checked17743 : (cuts17743.take 2).map (fun c => (2329542657-1+2*2^9*c.k,98465015785634+c.lower,98465395221520+c.upper)) = pointBounds17743 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000241
