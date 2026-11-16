import PlattPointSubsetKernel
import PlattPointPackets.S5B000310
import PlattPointPackets.S5B000311
import PlattPointPackets.S5B000312
import PlattPointPackets.S6B000000
import PlattPointPackets.S6B000001
import PlattPointPackets.S6B000002
import PlattPointPackets.S6B000003
import PlattPointPackets.S6B000004
import PlattPointPackets.S6B000005
import PlattPointPackets.S6B000006
import PlattPointPackets.S6B000007
import PlattPointPackets.S6B000008
import PlattPointPackets.S6B000009
import PlattPointPackets.S6B000010
import PlattPointPackets.S6B000011
import PlattGlobalGrid.S8B000064
namespace ChenEffective.PlattWindow.PointCovers.S8B000064
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((ChenEffective.PlattWindow.PointPackets.S5B000310.points ++ ChenEffective.PlattWindow.PointPackets.S5B000311.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000312.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000000.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000001.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000002.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000003.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000004.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000005.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000006.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000007.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000008.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000009.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000010.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000011.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000064.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000064.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000064
