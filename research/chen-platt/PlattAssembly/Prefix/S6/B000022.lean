import PlattAssemblyKernel
import PlattCertificates.Count131072.C050704
import PlattCertificates.Count131072.C050705
import PlattCertificates.Count131072.C050706
import PlattCertificates.Count131072.C050707
import PlattCertificates.Count131072.C050708
import PlattCertificates.Count131072.C050709
import PlattCertificates.Count131072.C050710
import PlattCertificates.Count131072.C050711
import PlattCertificates.Count131072.C050712
import PlattCertificates.Count131072.C050713
import PlattCertificates.Count131072.C050714
import PlattCertificates.Count131072.C050715
import PlattCertificates.Count131072.C050716
import PlattCertificates.Count131072.C050717
import PlattCertificates.Count131072.C050718
import PlattCertificates.Count131072.C050719
import PlattCertificates.Count131072.C050720
import PlattCertificates.Count131072.C050721
import PlattCertificates.Count131072.C050722
import PlattCertificates.Count131072.C050723
import PlattCertificates.Count131072.C050724
import PlattCertificates.Count131072.C050725
import PlattCertificates.Count131072.C050726
import PlattCertificates.Count131072.C050727
import PlattCertificates.Count131072.C050728
import PlattCertificates.Count131072.C050729
import PlattCertificates.Count131072.C050730
import PlattCertificates.Count131072.C050731
import PlattCertificates.Count131072.C050732
import PlattCertificates.Count131072.C050733
import PlattCertificates.Count131072.C050734
import PlattCertificates.Count131072.C050735
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50704 : List PrefixCut := [⟨48,184042012,184042118⟩,
⟨64,246475151,246475293⟩]
theorem checked50704 : checkPrefixCuts (2^48) 6649806849 10 Manual.Count131072.C050704.packed 64 cuts50704 = true := by
 decide +kernel
def pointBounds50704 : List (Nat × Nat × Nat) := [(6649905152,111831009828854,111831397050040)]
theorem point_links_checked50704 : (cuts50704.take 1).map (fun c => (6649806849-1+2*2^10*c.k,111830825786842+c.lower,111831213007922+c.upper)) = pointBounds50704 := by
 decide +kernel
def cuts50705 : List PrefixCut := [⟨64,249221562,249221702⟩]
theorem checked50705 : checkPrefixCuts (2^48) 6649937921 10 Manual.Count131072.C050705.packed 64 cuts50705 = true := by
 decide +kernel
def cuts50706 : List PrefixCut := [⟨22,85541796,85541845⟩,
⟨64,248497101,248497245⟩]
theorem checked50706 : checkPrefixCuts (2^48) 6650068993 10 Manual.Count131072.C050706.packed 64 cuts50706 = true := by
 decide +kernel
def pointBounds50706 : List (Nat × Nat × Nat) := [(6650114048,111831407025351,111831794246762)]
theorem point_links_checked50706 : (cuts50706.take 1).map (fun c => (6650068993-1+2*2^10*c.k,111831321483555+c.lower,111831708704917+c.upper)) = pointBounds50706 := by
 decide +kernel
def cuts50707 : List PrefixCut := [⟨60,228895715,228895844⟩,
⟨64,243116905,243117042⟩]
theorem checked50707 : checkPrefixCuts (2^48) 6650200065 10 Manual.Count131072.C050707.packed 64 cuts50707 = true := by
 decide +kernel
def pointBounds50707 : List (Nat × Nat × Nat) := [(6650322944,111831798876371,111832186098006)]
theorem point_links_checked50707 : (cuts50707.take 1).map (fun c => (6650200065-1+2*2^10*c.k,111831569980656+c.lower,111831957202162+c.upper)) = pointBounds50707 := by
 decide +kernel
def cuts50708 : List PrefixCut := [⟨64,246498066,246498204⟩]
theorem checked50708 : checkPrefixCuts (2^48) 6650331137 10 Manual.Count131072.C050708.packed 64 cuts50708 = true := by
 decide +kernel
def cuts50709 : List PrefixCut := [⟨34,129468784,129468856⟩,
⟨64,243107302,243107442⟩]
theorem checked50709 : checkPrefixCuts (2^48) 6650462209 10 Manual.Count131072.C050709.packed 64 cuts50709 = true := by
 decide +kernel
def pointBounds50709 : List (Nat × Nat × Nat) := [(6650531840,111832189064411,111832576286264)]
theorem point_links_checked50709 : (cuts50709.take 1).map (fun c => (6650462209-1+2*2^10*c.k,111832059595627+c.lower,111832446817408+c.upper)) = pointBounds50709 := by
 decide +kernel
def cuts50710 : List PrefixCut := [⟨64,244668452,244668594⟩]
theorem checked50710 : checkPrefixCuts (2^48) 6650593281 10 Manual.Count131072.C050710.packed 64 cuts50710 = true := by
 decide +kernel
def cuts50711 : List PrefixCut := [⟨8,30556768,30556785⟩,
⟨64,248387963,248388110⟩]
theorem checked50711 : checkPrefixCuts (2^48) 6650724353 10 Manual.Count131072.C050711.packed 64 cuts50711 = true := by
 decide +kernel
def pointBounds50711 : List (Nat × Nat × Nat) := [(6650740736,111832577928149,111832965150229)]
theorem point_links_checked50711 : (cuts50711.take 1).map (fun c => (6650724353-1+2*2^10*c.k,111832547371381+c.lower,111832934593444+c.upper)) = pointBounds50711 := by
 decide +kernel
def cuts50712 : List PrefixCut := [⟨46,176649128,176649233⟩,
⟨64,245335936,245336080⟩]
theorem checked50712 : checkPrefixCuts (2^48) 6650855425 10 Manual.Count131072.C050712.packed 64 cuts50712 = true := by
 decide +kernel
def pointBounds50712 : List (Nat × Nat × Nat) := [(6650949632,111832972408472,111833359630787)]
theorem point_links_checked50712 : (cuts50712.take 1).map (fun c => (6650855425-1+2*2^10*c.k,111832795759344+c.lower,111833182981554+c.upper)) = pointBounds50712 := by
 decide +kernel
def cuts50713 : List PrefixCut := [⟨64,244950219,244950356⟩]
theorem checked50713 : checkPrefixCuts (2^48) 6650986497 10 Manual.Count131072.C050713.packed 64 cuts50713 = true := by
 decide +kernel
def cuts50714 : List PrefixCut := [⟨20,75879415,75879458⟩,
⟨64,247188314,247188453⟩]
theorem checked50714 : checkPrefixCuts (2^48) 6651117569 10 Manual.Count131072.C050714.packed 64 cuts50714 = true := by
 decide +kernel
def pointBounds50714 : List (Nat × Nat × Nat) := [(6651158528,111833361924914,111833749147448)]
theorem point_links_checked50714 : (cuts50714.take 1).map (fun c => (6651117569-1+2*2^10*c.k,111833286045499+c.lower,111833673267990+c.upper)) = pointBounds50714 := by
 decide +kernel
def cuts50715 : List PrefixCut := [⟨58,220015067,220015197⟩,
⟨64,243713321,243713465⟩]
theorem checked50715 : checkPrefixCuts (2^48) 6651248641 10 Manual.Count131072.C050715.packed 64 cuts50715 = true := by
 decide +kernel
def pointBounds50715 : List (Nat × Nat × Nat) := [(6651367424,111833753248880,111834140471640)]
theorem point_links_checked50715 : (cuts50715.take 1).map (fun c => (6651248641-1+2*2^10*c.k,111833533233813+c.lower,111833920456443+c.upper)) = pointBounds50715 := by
 decide +kernel
def cuts50716 : List PrefixCut := [⟨64,244978053,244978188⟩]
theorem checked50716 : checkPrefixCuts (2^48) 6651379713 10 Manual.Count131072.C050716.packed 64 cuts50716 = true := by
 decide +kernel
def cuts50717 : List PrefixCut := [⟨32,120180942,120181013⟩,
⟨64,241207028,241207168⟩]
theorem checked50717 : checkPrefixCuts (2^48) 6651510785 10 Manual.Count131072.C050717.packed 64 cuts50717 = true := by
 decide +kernel
def pointBounds50717 : List (Nat × Nat × Nat) := [(6651576320,111834142106129,111834529329109)]
theorem point_links_checked50717 : (cuts50717.take 1).map (fun c => (6651510785-1+2*2^10*c.k,111834021925187+c.lower,111834409148096+c.upper)) = pointBounds50717 := by
 decide +kernel
def cuts50718 : List PrefixCut := [⟨64,245306936,245307073⟩]
theorem checked50718 : checkPrefixCuts (2^48) 6651641857 10 Manual.Count131072.C050718.packed 64 cuts50718 = true := by
 decide +kernel
def cuts50719 : List PrefixCut := [⟨6,24500808,24500822⟩,
⟨64,247883346,247883484⟩]
theorem checked50719 : checkPrefixCuts (2^48) 6651772929 10 Manual.Count131072.C050719.packed 64 cuts50719 = true := by
 decide +kernel
def pointBounds50719 : List (Nat × Nat × Nat) := [(6651785216,111834532939959,111834920163159)]
theorem point_links_checked50719 : (cuts50719.take 1).map (fun c => (6651772929-1+2*2^10*c.k,111834508439151+c.lower,111834895662337+c.upper)) = pointBounds50719 := by
 decide +kernel
def cuts50720 : List PrefixCut := [⟨44,171712843,171712939⟩,
⟨64,247116805,247116945⟩]
theorem checked50720 : checkPrefixCuts (2^48) 6651904001 10 Manual.Count131072.C050720.packed 64 cuts50720 = true := by
 decide +kernel
def pointBounds50720 : List (Nat × Nat × Nat) := [(6651994112,111834928035340,111835315258760)]
theorem point_links_checked50720 : (cuts50720.take 1).map (fun c => (6651904001-1+2*2^10*c.k,111834756322497+c.lower,111835143545821+c.upper)) = pointBounds50720 := by
 decide +kernel
def cuts50721 : List PrefixCut := [⟨64,245207804,245207940⟩]
theorem checked50721 : checkPrefixCuts (2^48) 6652035073 10 Manual.Count131072.C050721.packed 64 cuts50721 = true := by
 decide +kernel
def cuts50722 : List PrefixCut := [⟨18,70112893,70112933⟩,
⟨64,247784085,247784223⟩]
theorem checked50722 : checkPrefixCuts (2^48) 6652166145 10 Manual.Count131072.C050722.packed 64 cuts50722 = true := by
 decide +kernel
def pointBounds50722 : List (Nat × Nat × Nat) := [(6652203008,111835318759999,111835705983639)]
theorem point_links_checked50722 : (cuts50722.take 1).map (fun c => (6652166145-1+2*2^10*c.k,111835248647106+c.lower,111835635870706+c.upper)) = pointBounds50722 := by
 decide +kernel
def cuts50723 : List PrefixCut := [⟨56,213549024,213549145⟩,
⟨64,243674922,243675059⟩]
theorem checked50723 : checkPrefixCuts (2^48) 6652297217 10 Manual.Count131072.C050723.packed 64 cuts50723 = true := by
 decide +kernel
def pointBounds50723 : List (Nat × Nat × Nat) := [(6652411904,111835709980215,111836097204074)]
theorem point_links_checked50723 : (cuts50723.take 1).map (fun c => (6652297217-1+2*2^10*c.k,111835496431191+c.lower,111835883654929+c.upper)) = pointBounds50723 := by
 decide +kernel
def cuts50724 : List PrefixCut := [⟨64,241131438,241131574⟩]
theorem checked50724 : checkPrefixCuts (2^48) 6652428289 10 Manual.Count131072.C050724.packed 64 cuts50724 = true := by
 decide +kernel
def cuts50725 : List PrefixCut := [⟨30,117200285,117200351⟩,
⟨64,247219396,247219537⟩]
theorem checked50725 : checkPrefixCuts (2^48) 6652559361 10 Manual.Count131072.C050725.packed 64 cuts50725 = true := by
 decide +kernel
def pointBounds50725 : List (Nat × Nat × Nat) := [(6652620800,111836098437836,111836485661913)]
theorem point_links_checked50725 : (cuts50725.take 1).map (fun c => (6652559361-1+2*2^10*c.k,111835981237551+c.lower,111836368461562+c.upper)) = pointBounds50725 := by
 decide +kernel
def cuts50726 : List PrefixCut := [⟨64,245014400,245014536⟩]
theorem checked50726 : checkPrefixCuts (2^48) 6652690433 10 Manual.Count131072.C050726.packed 64 cuts50726 = true := by
 decide +kernel
def cuts50727 : List PrefixCut := [⟨4,16162067,16162076⟩,
⟨64,244417276,244417411⟩]
theorem checked50727 : checkPrefixCuts (2^48) 6652821505 10 Manual.Count131072.C050727.packed 64 cuts50727 = true := by
 decide +kernel
def pointBounds50727 : List (Nat × Nat × Nat) := [(6652829696,111836489633414,111836876857711)]
theorem point_links_checked50727 : (cuts50727.take 1).map (fun c => (6652821505-1+2*2^10*c.k,111836473471347+c.lower,111836860695635+c.upper)) = pointBounds50727 := by
 decide +kernel
def cuts50728 : List PrefixCut := [⟨42,158274209,158274295⟩,
⟨64,242381671,242381807⟩]
theorem checked50728 : checkPrefixCuts (2^48) 6652952577 10 Manual.Count131072.C050728.packed 64 cuts50728 = true := by
 decide +kernel
def pointBounds50728 : List (Nat × Nat × Nat) := [(6653038592,111836876162832,111837263387341)]
theorem point_links_checked50728 : (cuts50728.take 1).map (fun c => (6652952577-1+2*2^10*c.k,111836717888623+c.lower,111837105113046+c.upper)) = pointBounds50728 := by
 decide +kernel
def cuts50729 : List PrefixCut := [⟨64,244999922,245000059⟩]
theorem checked50729 : checkPrefixCuts (2^48) 6653083649 10 Manual.Count131072.C050729.packed 64 cuts50729 = true := by
 decide +kernel
def cuts50730 : List PrefixCut := [⟨16,62402086,62402119⟩,
⟨64,248506543,248506680⟩]
theorem checked50730 : checkPrefixCuts (2^48) 6653214721 10 Manual.Count131072.C050730.packed 64 cuts50730 = true := by
 decide +kernel
def pointBounds50730 : List (Nat × Nat × Nat) := [(6653247488,111837267672302,111837654897031)]
theorem point_links_checked50730 : (cuts50730.take 1).map (fun c => (6653214721-1+2*2^10*c.k,111837205270216+c.lower,111837592494912+c.upper)) = pointBounds50730 := by
 decide +kernel
def cuts50731 : List PrefixCut := [⟨54,208523399,208523516⟩,
⟨64,248713147,248713287⟩]
theorem checked50731 : checkPrefixCuts (2^48) 6653345793 10 Manual.Count131072.C050731.packed 64 cuts50731 = true := by
 decide +kernel
def pointBounds50731 : List (Nat × Nat × Nat) := [(6653456384,111837662300158,111838049525108)]
theorem point_links_checked50731 : (cuts50731.take 1).map (fun c => (6653345793-1+2*2^10*c.k,111837453776759+c.lower,111837841001592+c.upper)) = pointBounds50731 := by
 decide +kernel
def cuts50732 : List PrefixCut := [⟨64,244816212,244816347⟩]
theorem checked50732 : checkPrefixCuts (2^48) 6653476865 10 Manual.Count131072.C050732.packed 64 cuts50732 = true := by
 decide +kernel
def cuts50733 : List PrefixCut := [⟨28,107451956,107452014⟩,
⟨64,243584621,243584760⟩]
theorem checked50733 : checkPrefixCuts (2^48) 6653607937 10 Manual.Count131072.C050733.packed 64 cuts50733 = true := by
 decide +kernel
def pointBounds50733 : List (Nat × Nat × Nat) := [(6653665280,111838054758074,111838441983240)]
theorem point_links_checked50733 : (cuts50733.take 1).map (fun c => (6653607937-1+2*2^10*c.k,111837947306118+c.lower,111838334531226+c.upper)) = pointBounds50733 := by
 decide +kernel
def cuts50734 : List PrefixCut := [⟨64,246033367,246033508⟩]
theorem checked50734 : checkPrefixCuts (2^48) 6653739009 10 Manual.Count131072.C050734.packed 64 cuts50734 = true := by
 decide +kernel
def cuts50735 : List PrefixCut := [⟨2,7276016,7276021⟩,
⟨64,245351694,245351834⟩]
theorem checked50735 : checkPrefixCuts (2^48) 6653870081 10 Manual.Count131072.C050735.packed 64 cuts50735 = true := by
 decide +kernel
def pointBounds50735 : List (Nat × Nat × Nat) := [(6653874176,111838444200122,111838831425515)]
theorem point_links_checked50735 : (cuts50735.take 1).map (fun c => (6653870081-1+2*2^10*c.k,111838436924106+c.lower,111838824149494+c.upper)) = pointBounds50735 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000022
