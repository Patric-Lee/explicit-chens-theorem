import PlattPointSubsetKernel
import PlattPointPackets.S4B000308
import PlattPointPackets.S4B000309
import PlattPointPackets.S4B000310
import PlattPointPackets.S4B000311
import PlattPointPackets.S4B000312
import PlattPointPackets.S5B000000
import PlattPointPackets.S5B000001
import PlattPointPackets.S5B000002
import PlattPointPackets.S5B000003
import PlattPointPackets.S5B000004
import PlattPointPackets.S5B000005
import PlattPointPackets.S5B000006
import PlattGlobalGrid.S8B000036
namespace ChenEffective.PlattWindow.PointCovers.S8B000036
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((ChenEffective.PlattWindow.PointPackets.S4B000308.points ++ ChenEffective.PlattWindow.PointPackets.S4B000309.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000310.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000311.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000312.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000000.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000001.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000002.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000003.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000004.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000005.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000006.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000036.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000036.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000036
