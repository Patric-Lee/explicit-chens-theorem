import PlattPointSubsetKernel
import PlattPointPackets.S5B000078
import PlattPointPackets.S5B000079
import PlattPointPackets.S5B000080
import PlattPointPackets.S5B000081
import PlattPointPackets.S5B000082
import PlattPointPackets.S5B000083
import PlattPointPackets.S5B000084
import PlattPointPackets.S5B000085
import PlattPointPackets.S5B000086
import PlattPointPackets.S5B000087
import PlattPointPackets.S5B000088
import PlattPointPackets.S5B000089
import PlattGlobalGrid.S8B000044
namespace ChenEffective.PlattWindow.PointCovers.S8B000044
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((ChenEffective.PlattWindow.PointPackets.S5B000078.points ++ ChenEffective.PlattWindow.PointPackets.S5B000079.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000080.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000081.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000082.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000083.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000084.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000085.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000086.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000087.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000088.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000089.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000044.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000044.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000044
