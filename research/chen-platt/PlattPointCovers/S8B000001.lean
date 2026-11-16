import PlattPointSubsetKernel
import PlattPointPackets.S4B000002
import PlattPointPackets.S4B000003
import PlattPointPackets.S4B000004
import PlattPointPackets.S4B000005
import PlattPointPackets.S4B000006
import PlattPointPackets.S4B000007
import PlattPointPackets.S4B000008
import PlattPointPackets.S4B000009
import PlattGlobalGrid.S8B000001
namespace ChenEffective.PlattWindow.PointCovers.S8B000001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S4B000002.points ++ ChenEffective.PlattWindow.PointPackets.S4B000003.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000004.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000005.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000006.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000007.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000008.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000009.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000001.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000001.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000001
