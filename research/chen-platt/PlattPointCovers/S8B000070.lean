import PlattPointSubsetKernel
import PlattPointPackets.S6B000075
import PlattPointPackets.S6B000076
import PlattPointPackets.S6B000077
import PlattPointPackets.S6B000078
import PlattPointPackets.S6B000079
import PlattPointPackets.S6B000080
import PlattPointPackets.S6B000081
import PlattPointPackets.S6B000082
import PlattPointPackets.S6B000083
import PlattPointPackets.S6B000084
import PlattPointPackets.S6B000085
import PlattPointPackets.S6B000086
import PlattPointPackets.S6B000087
import PlattPointPackets.S6B000088
import PlattGlobalGrid.S8B000070
namespace ChenEffective.PlattWindow.PointCovers.S8B000070
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000075.points ++ ChenEffective.PlattWindow.PointPackets.S6B000076.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000077.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000078.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000079.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000080.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000081.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000082.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000083.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000084.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000085.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000086.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000087.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000088.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000070.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000070.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000070
